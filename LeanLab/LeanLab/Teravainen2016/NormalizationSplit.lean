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
import LeanLab.PNTPort.PsiChi.Final

open Finset
open Real
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



/-- A nonprincipal Dirichlet character mod 4, with its values on the integers. -/
private theorem chi4_exists :
    ∃ χ : DirichletCharacter ℂ 4, χ ≠ 1 ∧ χ (3 : ZMod 4) = -1 ∧ χ (2 : ZMod 4) = 0 ∧
      ∀ n : ℕ, χ (n : ZMod 4) = if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0 := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (M := ZMod 4) (R := ℂ) (a := (3 : ZMod 4)) (by decide)
  have hone : (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime 3 4).mpr (by decide))
  have hne : χ ≠ 1 := fun h => hχ (by rw [h]; exact hone)
  have hsq : χ (3 : ZMod 4) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, show (3 : ZMod 4) * 3 = 1 by decide, map_one]
  have h3 : χ (3 : ZMod 4) = -1 := by
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact absurd h hχ
    · exact h
  have h2 : ¬ IsUnit (2 : ZMod 4) := by
    intro h
    have hc : Nat.Coprime 2 4 := (ZMod.isUnit_iff_coprime 2 4).mp h
    exact absurd hc (by decide)
  have v0 : χ (0 : ZMod 4) = 0 := MulChar.map_zero χ
  have v1 : χ (1 : ZMod 4) = 1 := map_one χ
  have v2 : χ (2 : ZMod 4) = 0 := MulChar.map_nonunit χ h2
  refine ⟨χ, hne, h3, v2, ?_⟩
  intro n
  have hmod : (n : ZMod 4) = ((n % 4 : ℕ) : ZMod 4) :=
    (ZMod.natCast_eq_natCast_iff' n (n % 4) 4).mpr (by rw [Nat.mod_mod])
  rw [hmod]
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 4
  · simpa using v0
  · simpa using v1
  · simpa using v2
  · simpa using h3

/-- The Siegel-Walfisz bound for ψ(x, χ) at level 4, made uniform over all x ≥ 2. -/
private theorem psi_chi4_bound {χ : DirichletCharacter ℂ 4} (hχ : χ ≠ 1) :
    ∃ c K : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x →
      ‖LeanLab.PNTPort.BV.psiChi x χ‖ ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  obtain ⟨c, K, hc, H⟩ := LeanLab.PNTPort.PsiChi.psiChi_nonprincipal_bound 1 one_pos
  refine ⟨c, max K (4 * Real.exp (2 * c)), hc, ?_⟩
  intro x hx
  have hKle : K ≤ max K (4 * Real.exp (2 * c)) := le_max_left _ _
  rcases le_or_gt (Real.exp 4) x with hbig | hsmall
  · have hlog : (4 : ℝ) ≤ Real.log x ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      calc (4 : ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 4) hbig
    have h := H x hx 4 χ hχ hlog
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_right hKle (by linarith : (0:ℝ) ≤ x)
  · have hlogx : Real.log x ≤ 4 := by
      calc Real.log x ≤ Real.log (Real.exp 4) := Real.log_le_log (by linarith) hsmall.le
        _ = 4 := Real.log_exp 4
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hsqrt : Real.sqrt (Real.log x) ≤ 2 := by
      have h := Real.sqrt_le_sqrt hlogx
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h4] at h
    have hexp : Real.exp (-c * Real.sqrt (Real.log x)) ≥ Real.exp (-(2 * c)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hc]
    have hpsi : ‖LeanLab.PNTPort.BV.psiChi x χ‖ ≤ 4 * x := by
      unfold LeanLab.PNTPort.BV.psiChi
      have h1 : ‖∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4)‖ ≤
          ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro n _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hχ1 := DirichletCharacter.norm_le_one χ (n : ZMod 4)
        have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        nlinarith
      have h2 : ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ≤
          (⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ := by
        have hcard : (∑ _n ∈ Icc 1 ⌊x⌋₊, (1 : ℝ)) = (⌊x⌋₊ : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          norm_num
        have hm2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
        calc ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n
            ≤ ∑ _n ∈ Icc 1 ⌊x⌋₊, Real.log ⌊x⌋₊ := by
              apply Finset.sum_le_sum
              intro n hn
              have hnm : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hn).2
              have hle := ArithmeticFunction.vonMangoldt_le_log (n := n)
              have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
              have hl : Real.log n ≤ Real.log ⌊x⌋₊ :=
                Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnm)
              linarith
          _ = (⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
              norm_num
      have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hm2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
      have hlogm : Real.log ⌊x⌋₊ ≤ 4 :=
        le_trans (Real.log_le_log (by positivity) hfloor) hlogx
      have hm0 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
      calc ‖∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4)‖
          ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := h1
        _ ≤ (⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ := h2
        _ ≤ x * 4 := by nlinarith
        _ = 4 * x := by ring
    calc ‖LeanLab.PNTPort.BV.psiChi x χ‖ ≤ 4 * x := hpsi
      _ = (4 * Real.exp (2 * c)) * x * Real.exp (-(2 * c)) := by
          have he : Real.exp (2 * c) * Real.exp (-(2 * c)) = 1 := by
            rw [← Real.exp_add, show 2 * c + -(2 * c) = 0 by ring, Real.exp_zero]
          calc 4 * x = 4 * x * 1 := by ring
            _ = 4 * x * (Real.exp (2 * c) * Real.exp (-(2 * c))) := by rw [he]
            _ = (4 * Real.exp (2 * c)) * x * Real.exp (-(2 * c)) := by ring
      _ ≤ max K (4 * Real.exp (2 * c)) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
          have h4 : (4 : ℝ) * Real.exp (2 * c) ≤ max K (4 * Real.exp (2 * c)) := le_max_right _ _
          have hx0 : (0 : ℝ) < x := by linarith
          have he : Real.exp (-(2 * c)) ≤ Real.exp (-c * Real.sqrt (Real.log x)) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hc]
          have hleft : (4 * Real.exp (2 * c)) * x * Real.exp (-(2 * c)) ≤
              max K (4 * Real.exp (2 * c)) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
            have hA : (0:ℝ) ≤ (4 * Real.exp (2 * c)) * x := by positivity
            have hB : (4 * Real.exp (2 * c)) * x ≤ max K (4 * Real.exp (2 * c)) * x :=
              mul_le_mul_of_nonneg_right h4 hx0.le
            calc (4 * Real.exp (2 * c)) * x * Real.exp (-(2 * c))
                ≤ max K (4 * Real.exp (2 * c)) * x * Real.exp (-(2 * c)) :=
                  mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
              _ ≤ max K (4 * Real.exp (2 * c)) * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
                  mul_le_mul_of_nonneg_left he (by positivity)
          exact hleft

/-- The integral of `exp (-c √log t) / t` over `[a, b]` for `1 < a ≤ b`, bounded by the
antiderivative `-(2/c²)(c√log t + 1) exp (-c√log t)` evaluated at `a`. -/
private theorem integral_exp_sqrtlog_div {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.exp (-c * Real.sqrt (Real.log t)) / t ≤
      2 / c ^ 2 * (c * Real.sqrt (Real.log a) + 1) *
        Real.exp (-c * Real.sqrt (Real.log a)) := by
  set G : ℝ → ℝ := fun t => -(2 / c ^ 2) * ((c * Real.sqrt (Real.log t) + 1) *
    Real.exp (-c * Real.sqrt (Real.log t))) with hG
  have ha0 : (0 : ℝ) < a := by linarith
  have ht1 : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt G (Real.exp (-c * Real.sqrt (Real.log t)) / t) t := by
    intro t ht
    have ht1' := ht1 t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hlpos : 0 < Real.log t := Real.log_pos ht1'
    have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (Real.log t))
        ((1 : ℝ) / (2 * Real.sqrt (Real.log t)) * (1 / t)) t := by
      have h1 : HasDerivAt Real.log ((t : ℝ)⁻¹) t := Real.hasDerivAt_log ht0.ne'
      have h2 := h1.sqrt hlpos.ne'
      convert h2 using 1
      field_simp
    have hinner : HasDerivAt (fun t : ℝ => (c * Real.sqrt (Real.log t) + 1) *
        Real.exp (-c * Real.sqrt (Real.log t)))
        ((c * (1 / (2 * Real.sqrt (Real.log t)) * (1 / t))) *
          Real.exp (-c * Real.sqrt (Real.log t)) +
          (c * Real.sqrt (Real.log t) + 1) *
            (Real.exp (-c * Real.sqrt (Real.log t)) *
              (-c * (1 / (2 * Real.sqrt (Real.log t)) * (1 / t))))) t := by
      have hA : HasDerivAt (fun t : ℝ => c * Real.sqrt (Real.log t) + 1)
          (c * (1 / (2 * Real.sqrt (Real.log t)) * (1 / t)) + 0) t := by
        simpa using (hsq.const_mul c).add_const 1
      have hB : HasDerivAt (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)))
          (Real.exp (-c * Real.sqrt (Real.log t)) *
            (-c * (1 / (2 * Real.sqrt (Real.log t)) * (1 / t)))) t := by
        have h3 : HasDerivAt (fun t : ℝ => -c * Real.sqrt (Real.log t))
            (-c * (1 / (2 * Real.sqrt (Real.log t)) * (1 / t))) t := hsq.const_mul (-c)
        simpa using h3.exp
      have hmul := hA.mul hB
      convert hmul using 1
      ring
    have hfin := hinner.const_mul (-(2 / c ^ 2))
    refine hfin.congr_deriv ?_
    have hs : Real.sqrt (Real.log t) ≠ 0 := (Real.sqrt_pos.mpr hlpos).ne'
    have hcne : c ≠ 0 := hc.ne'
    have he : Real.exp (-c * Real.sqrt (Real.log t)) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
      (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht1' : 1 < t := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := first | positivity | linarith)
  have hInt : IntervalIntegrable (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
      MeasureTheory.volume a b := hcont.intervalIntegrable
  have hfun : (∫ t in a..b, Real.exp (-c * Real.sqrt (Real.log t)) / t) = G b - G a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
  have hGb : G b ≤ 0 := by
    have hb1 : 1 < b := lt_of_lt_of_le ha hab
    have hpos : 0 < 2 / c ^ 2 := by positivity
    have harg : 0 < (c * Real.sqrt (Real.log b) + 1) * Real.exp (-c * Real.sqrt (Real.log b)) := by
      have : 0 < Real.sqrt (Real.log b) := Real.sqrt_pos.mpr (Real.log_pos hb1)
      positivity
    simp only [hG]
    nlinarith
  have hGa : G a = -(2 / c ^ 2 * (c * Real.sqrt (Real.log a) + 1) *
      Real.exp (-c * Real.sqrt (Real.log a))) := by
    simp only [hG]; ring
  rw [hfun, hGa]
  linarith

/-- Abel summation turns the Siegel-Walfisz bound for `ψ(x, χ)` into a uniform bound for the
`χ`-twisted von Mangoldt sum `∑_{n ≤ x} Λ(n) χ(n) / n`. -/
private theorem sum_chi_mangoldt_div_bound {χ : DirichletCharacter ℂ 4} (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n‖ ≤ C := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  obtain ⟨c₀, K, hc, hK⟩ := psi_chi4_bound hχ
  have h2nu : ¬ IsUnit (2 : ZMod 4) := by
    intro h
    have hc2 : Nat.Coprime 2 4 := (ZMod.isUnit_iff_coprime 2 4).mp h
    exact absurd hc2 (by decide)
  set K' := max K 1 with hK'def
  have hK'K : K ≤ K' := le_max_left _ _
  have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
  have hK'0 : (0 : ℝ) < K' := lt_of_lt_of_le one_pos hK'1
  have hK'b : ∀ x : ℝ, 2 ≤ x →
      ‖LeanLab.PNTPort.BV.psiChi x χ‖ ≤ K' * x * Real.exp (-c₀ * Real.sqrt (Real.log x)) := by
    intro x hx
    refine (hK x hx).trans ?_
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_right hK'K (by linarith)
  set B : ℝ := 2 / c₀ ^ 2 * (c₀ * Real.sqrt (Real.log 2) + 1) *
    Real.exp (-c₀ * Real.sqrt (Real.log 2)) with hBdef
  have hBle : B ≤ 2 / c₀ ^ 2 * (c₀ * Real.sqrt (Real.log 2) + 1) *
      Real.exp (-c₀ * Real.sqrt (Real.log 2)) := le_of_eq hBdef
  refine ⟨2 * K' + K' * B, by positivity, ?_⟩
  intro x hx
  have hx0 : (0 : ℝ) < x := by linarith
  set f : ℝ → ℂ := fun t => ((t : ℂ))⁻¹ with hf
  set cc : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k : ℂ) * χ (k : ZMod 4) with hcdef
  -- the summatory function is psi
  have hA : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, cc k = LeanLab.PNTPort.BV.psiChi t χ := by
    intro t
    have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
      rintro ⟨p, k, hp, hk, hpk⟩
      have hpos : 0 < p ^ k := pow_pos (by have := hp.two_le; omega) k
      omega
    have hset : Ioc 0 ⌊t⌋₊ = Icc 1 ⌊t⌋₊ := by
      ext n; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega
    simp only [hcdef]
    unfold LeanLab.PNTPort.BV.psiChi
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hset]
    simp only [h0, Complex.ofReal_zero, zero_mul, zero_add]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ f t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < t := by linarith [ht.1]
      exact_mod_cast hpos.ne'
    simp only [hf]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    exact (h1.inv ht0).differentiableAt
  have hderivval : ∀ t ∈ Set.Icc (2 : ℝ) x, deriv f t = -1 / ((t : ℂ) ^ 2) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < t := by linarith [ht.1]
      exact_mod_cast hpos.ne'
    simp only [hf]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    exact (h1.inv ht0).deriv
  have hIntF : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (2 : ℝ) x) := by
    simp only [hf]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0r : (0 : ℝ) < t := by linarith [ht.1]
    have ht0c : (t : ℂ) ≠ 0 := by exact_mod_cast ht0r.ne'
    have hev : ∀ᶠ s : ℝ in nhds t, (s : ℂ) ≠ 0 := by
      have hU : IsOpen {s : ℝ | (s : ℂ) ≠ 0} := by
        have hE : {s : ℝ | (s : ℂ) ≠ 0} = Complex.ofReal ⁻¹' ({0}ᶜ : Set ℂ) := by
          ext s; simp
        rw [hE]
        exact isOpen_compl_singleton.preimage Complex.continuous_ofReal
      exact hU.mem_nhds ht0c
    have heq : (fun s : ℝ => -1 / ((s : ℂ)) ^ 2) =ᶠ[nhds t]
        deriv (fun s : ℝ => ((s : ℂ))⁻¹) := by
      filter_upwards [hev] with s hs
      exact (((Complex.ofRealCLM.hasDerivAt (x := s)).inv hs).deriv).symm
    have hcont : ContinuousAt (fun s : ℝ => -1 / ((s : ℂ)) ^ 2) t := by
      refine ContinuousAt.div continuousAt_const ?_ (pow_ne_zero 2 ht0c)
      fun_prop
    exact (hcont.congr heq).continuousWithinAt
  have habel := sum_mul_eq_sub_sub_integral_mul (c := cc) (f := f) (a := 2) (b := x)
    (by norm_num) (by linarith) hdiff hIntF
  rw [Nat.floor_ofNat] at habel
  -- the small initial terms vanish
  -- the small initial terms vanish
  have hsmall : ∑ n ∈ (Finset.Icc 1 2 : Finset ℕ), f n * cc n = 0 := by
    have hI : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
    rw [hI, Finset.sum_pair (by norm_num)]
    have h2 : χ ((2 : ℕ) : ZMod 4) = 0 := MulChar.map_nonunit χ h2nu
    simp only [hf, hcdef]
    rw [ArithmeticFunction.vonMangoldt_apply_one, h2]
    norm_num
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hunion : Icc 1 ⌊x⌋₊ = Icc 1 2 ∪ Ioc 2 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Icc 1 2 : Finset ℕ) (Ioc 2 ⌊x⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_Ioc] at ha'
    omega
  have hgoal : ∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n =
      ∑ k ∈ Ioc 2 ⌊x⌋₊, f k * cc k := by
    have h1 : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n =
        f n * cc n := by
      intro n
      simp only [hf, hcdef, div_eq_inv_mul, Complex.ofReal_natCast]
    simp only [h1]
    rw [hunion, Finset.sum_union hdisj, hsmall, zero_add]
  -- bound the first Abel term
  have hterm1 : ‖f x * (∑ k ∈ Icc 0 ⌊x⌋₊, cc k)‖ ≤ K' := by
    rw [hA x, norm_mul]
    have hxinv : ‖f x‖ = 1 / x := by
      simp only [hf]
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, one_div]
    rw [hxinv]
    have hb := hK'b x hx
    have hexp1 : Real.exp (-c₀ * Real.sqrt (Real.log x)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      nlinarith [Real.sqrt_nonneg (Real.log x), hc]
    calc (1 / x) * ‖LeanLab.PNTPort.BV.psiChi x χ‖ ≤
          (1 / x) * (K' * x * Real.exp (-c₀ * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K' * Real.exp (-c₀ * Real.sqrt (Real.log x)) := by field_simp
      _ ≤ K' * 1 := mul_le_mul_of_nonneg_left hexp1 (le_of_lt hK'0)
      _ = K' := by ring
  -- the second Abel term
  have hterm2 : ‖f 2 * (∑ k ∈ (Finset.Icc 0 2 : Finset ℕ), cc k)‖ ≤ K' := by
    have hA2 : ∑ k ∈ (Finset.Icc 0 2 : Finset ℕ), cc k = LeanLab.PNTPort.BV.psiChi 2 χ := by
      rw [← hA 2, Nat.floor_ofNat]
    rw [hA2, norm_mul]
    have hf2 : ‖f 2‖ = 1 / 2 := by
      simp only [hf]
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hf2]
    have hb := hK'b 2 (by norm_num)
    have hexp2 : Real.exp (-c₀ * Real.sqrt (Real.log 2)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [Real.sqrt_nonneg (Real.log 2), hc]
    calc (1 / 2) * ‖LeanLab.PNTPort.BV.psiChi 2 χ‖ ≤
          (1 / 2) * (K' * 2 * Real.exp (-c₀ * Real.sqrt (Real.log 2))) := by
          apply mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = K' * Real.exp (-c₀ * Real.sqrt (Real.log 2)) := by field_simp
      _ ≤ K' * 1 := mul_le_mul_of_nonneg_left hexp2 (le_of_lt hK'0)
      _ = K' := by ring
  -- the integral term
  have hmaj : ∀ t ∈ Set.Ioc (2 : ℝ) x, ‖deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k)‖ ≤
      K' * (Real.exp (-c₀ * Real.sqrt (Real.log t)) / t) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht2' : 2 ≤ t := le_of_lt ht1
    have ht0 : (0 : ℝ) < t := by linarith
    rw [hA t, hderivval t (Set.mem_Icc.mpr ⟨ht2', ht2⟩), norm_mul]
    have hnorm : ‖(-1 / ((t : ℂ) ^ 2))‖ = 1 / (t * t) := by
      have htC : ‖((t : ℂ))‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      rw [norm_div, norm_neg, norm_one, norm_pow, htC, pow_two]
    rw [hnorm]
    have hb := hK'b t ht2'
    calc (1 / (t * t)) * ‖LeanLab.PNTPort.BV.psiChi t χ‖ ≤
          (1 / (t * t)) * (K' * t * Real.exp (-c₀ * Real.sqrt (Real.log t))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K' * (Real.exp (-c₀ * Real.sqrt (Real.log t)) / t) := by
          field_simp
  have hmajC : IntervalIntegrable (fun t : ℝ => K' *
      (Real.exp (-c₀ * Real.sqrt (Real.log t)) / t)) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := first | positivity | linarith)
  have hmajint : IntervalIntegrable (fun t : ℝ => K' *
      (Real.exp (-c₀ * Real.sqrt (Real.log t)) / t)) MeasureTheory.volume (min 2 x) (max 2 x) := by
    rw [min_eq_left (by linarith : (2:ℝ) ≤ x), max_eq_right (by linarith : (2:ℝ) ≤ x)]
    exact hmajC
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume)
    (f := fun t : ℝ => deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k))
    (g := fun t : ℝ => K' * (Real.exp (-c₀ * Real.sqrt (Real.log t)) / t))
    (by linarith : (2 : ℝ) ≤ x) (Filter.Eventually.of_forall hmaj) hmajC
  rw [intervalIntegral.integral_const_mul] at hbound
  have hint := integral_exp_sqrtlog_div hc (a := 2) (b := x) (by norm_num) (by linarith)
  have hint3 : K' * (∫ t in (2 : ℝ)..x, Real.exp (-c₀ * Real.sqrt (Real.log t)) / t) ≤ K' * B := by
    rw [hBdef]
    exact mul_le_mul_of_nonneg_left hint (le_of_lt hK'0)
  have hsetint : (∫ t in Set.Ioc (2 : ℝ) x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k)) =
      ∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  have hmain : ‖f x * (∑ k ∈ Icc 0 ⌊x⌋₊, cc k) - f 2 * (∑ k ∈ (Finset.Icc 0 2 : Finset ℕ), cc k) -
      ∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k)‖ ≤ 2 * K' + K' * B := by
    have h1 : ‖f x * (∑ k ∈ Icc 0 ⌊x⌋₊, cc k) - f 2 * (∑ k ∈ (Finset.Icc 0 2 : Finset ℕ), cc k) -
        ∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k)‖ ≤ (K' + K') + K' * B := by
      refine le_trans (norm_sub_le _ _) ?_
      refine le_trans (add_le_add (norm_sub_le _ _) le_rfl) ?_
      exact add_le_add (add_le_add hterm1 hterm2) (le_trans hbound hint3)
    have h2 : (K' + K') + K' * B = 2 * K' + K' * B := by ring
    rw [← h2]
    exact h1
  calc ‖∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n‖
      = ‖∑ k ∈ Ioc 2 ⌊x⌋₊, f k * cc k‖ := by rw [hgoal]
    _ = ‖f x * (∑ k ∈ Icc 0 ⌊x⌋₊, cc k) - f 2 * (∑ k ∈ (Finset.Icc 0 2 : Finset ℕ), cc k) -
        ∫ t in Set.Ioc (2 : ℝ) x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k)‖ := congrArg norm habel
    _ = ‖f x * (∑ k ∈ Icc 0 ⌊x⌋₊, cc k) - f 2 * (∑ k ∈ (Finset.Icc 0 2 : Finset ℕ), cc k) -
        ∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, cc k)‖ := by rw [hsetint]
    _ ≤ 2 * K' + K' * B := hmain


/-- `∫_a^b t^(-5/4) ≤ 4 a^(-1/4)` for `0 < a ≤ b`, from the antiderivative `-4 t^(-1/4)`. -/
private theorem integral_rpow_neg_five_quarters {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, t ^ (-(5 : ℝ) / 4) ≤ 4 * a ^ (-(1 : ℝ) / 4) := by
  set G : ℝ → ℝ := fun t => -4 * t ^ (-(1 : ℝ) / 4) with hG
  have hmem : ∀ t ∈ Set.uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2, ha, le_of_lt ha]
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt G (t ^ (-(5 : ℝ) / 4)) t := by
    intro t ht
    have ht0 := hmem t ht
    have h := (@Real.hasDerivAt_rpow_const t (-(1 : ℝ) / 4) (Or.inl ht0.ne')).const_mul (-4)
    have hval : -4 * (-(1 : ℝ) / 4 * t ^ (-(1 : ℝ) / 4 - 1)) = t ^ (-(5 : ℝ) / 4) := by
      rw [show -(1 : ℝ) / 4 - 1 = -(5 : ℝ) / 4 by norm_num]
      ring
    rw [hval] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(5 : ℝ) / 4)) (Set.uIcc a b) := by
    intro t ht
    have ht0 := hmem t ht
    exact (Real.continuousAt_rpow_const t (-(5 : ℝ) / 4) (Or.inl ht0.ne')).continuousWithinAt
  have hInt : IntervalIntegrable (fun t : ℝ => t ^ (-(5 : ℝ) / 4)) MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  have hfun := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ b ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hb.le _
  have h2 : 0 < a ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos ha _
  have hGa : G a = -4 * a ^ (-(1 : ℝ) / 4) := by simp only [hG]
  have hGb : G b ≤ 0 := by
    simp only [hG]
    nlinarith
  rw [hfun, hGa]
  linarith

/-- `∫_a^b 2 log t /(t √t) ≤ 32` for `1 < a ≤ b`. -/
private theorem integral_log_div_three_halves {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 2 * Real.log t / (t * Real.sqrt t) ≤ 32 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hmaj : ∀ t ∈ Set.Icc a b, 2 * Real.log t / (t * Real.sqrt t) ≤ 8 * t ^ (-(5 : ℝ) / 4) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hlog : Real.log t ≤ 4 * t ^ ((1 : ℝ) / 4) := by
      have h := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 4)
      calc Real.log t ≤ t ^ ((1 : ℝ) / 4) / (1 / 4) := h
        _ = 4 * t ^ ((1 : ℝ) / 4) := by ring
    have hpos : 0 < t * Real.sqrt t := by positivity
    have heq : t ^ ((1 : ℝ) / 4) / (t * Real.sqrt t) = t ^ (-(5 : ℝ) / 4) := by
      have hsq : (t : ℝ) * Real.sqrt t = t ^ ((3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        nth_rewrite 1 [show t = t ^ (1 : ℝ) from (Real.rpow_one t).symm]
        rw [← Real.rpow_add ht0]
        norm_num
      rw [hsq, ← Real.rpow_sub ht0]
      norm_num
    calc 2 * Real.log t / (t * Real.sqrt t)
        ≤ 8 * t ^ ((1 : ℝ) / 4) / (t * Real.sqrt t) := by
          rw [div_le_div_iff_of_pos_right hpos]
          linarith
      _ = 8 * (t ^ ((1 : ℝ) / 4) / (t * Real.sqrt t)) := by ring
      _ = 8 * t ^ (-(5 : ℝ) / 4) := by rw [heq]
  have hleft : IntervalIntegrable (fun t : ℝ => 2 * Real.log t / (t * Real.sqrt t))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;> (have ht0 : (0:ℝ) < t := by linarith [h.1, h.2, ha])
    · apply ContinuousAt.continuousWithinAt
      fun_prop (disch := first | positivity | linarith)
    · apply ContinuousAt.continuousWithinAt
      fun_prop (disch := first | positivity | linarith)
  have hright : IntervalIntegrable (fun t : ℝ => 8 * t ^ (-(5 : ℝ) / 4))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;> (have ht0 : (0:ℝ) < t := by linarith [h.1, h.2, ha])
    · exact (Real.continuousAt_rpow_const t (-(5 : ℝ) / 4) (Or.inl ht0.ne')).continuousWithinAt.const_mul 8
    · exact (Real.continuousAt_rpow_const t (-(5 : ℝ) / 4) (Or.inl ht0.ne')).continuousWithinAt.const_mul 8
  have hint : ∫ t in a..b, 2 * Real.log t / (t * Real.sqrt t) ≤
      ∫ t in a..b, 8 * t ^ (-(5 : ℝ) / 4) := by
    apply intervalIntegral.integral_mono_on hab hleft hright
    intro t ht
    exact hmaj t ht
  have h8 : ∫ t in a..b, 8 * t ^ (-(5 : ℝ) / 4) = 8 * ∫ t in a..b, t ^ (-(5 : ℝ) / 4) :=
    intervalIntegral.integral_const_mul 8 _
  rw [h8] at hint
  have hb := integral_rpow_neg_five_quarters ha0 hab
  have hle1 : a ^ (-(1 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt ha) (by norm_num)
  have hnn : 0 ≤ a ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg ha0.le _
  nlinarith [hint, hb, hle1, hnn]


/-- `ψ - θ` is the sum of `Λ` over the non-primes. -/
private theorem psi_sub_theta_eq_sum_nonprime (m : ℕ) :
    Chebyshev.psi m - Chebyshev.theta m =
      ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n := by
  have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
    rintro ⟨p, k, hp, hk, hpk⟩
    have hpos : 0 < p ^ k := pow_pos (by have := hp.two_le; omega) k
    omega
  have hpsi : Chebyshev.psi m = ∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast,
      Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons, h0, zero_add]
    have hset : (Finset.Ioc 0 m : Finset ℕ) = Finset.Icc 1 m := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hset]
  have htheta : Chebyshev.theta m =
      ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime), ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
    have hset : (Finset.Icc 0 m).filter (fun n => n.Prime)
        = (Finset.Icc 1 m).filter (fun n => n.Prime) := by
      ext n
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_Icc] at h ⊢
        exact ⟨⟨by have := h.2.two_le; omega, h.1.2⟩, h.2⟩
      · intro h
        simp only [Finset.mem_filter, Finset.mem_Icc] at h ⊢
        exact ⟨⟨Nat.zero_le _, h.1.2⟩, h.2⟩
    rw [hset]
    exact Finset.sum_congr rfl (fun p hp =>
      (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm)
  rw [hpsi, htheta,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 m) (fun n => n.Prime)
      (fun n => ArithmeticFunction.vonMangoldt n)]
  ring

/-- The non-prime part of the von Mangoldt sum with weight `1/n` is bounded uniformly. -/
private theorem sum_nonprime_mangoldt_div_le {x : ℝ} (hx : 2 ≤ x) :
    ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Prime),
      ArithmeticFunction.vonMangoldt n / n ≤ 40 := by
  have hx0 : (0 : ℝ) < x := by linarith
  set c : ℕ → ℝ := fun n => if n.Prime then 0 else ArithmeticFunction.vonMangoldt n with hc
  have h0c : c 0 = 0 := by
    have hΛ : ArithmeticFunction.vonMangoldt 0 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
      rintro ⟨p, k, hp, hk, hpk⟩
      have hpos : 0 < p ^ k := pow_pos (by have := hp.two_le; omega) k
      omega
    simp only [hc, hΛ]
    rw [if_neg (by decide : ¬ (0 : ℕ).Prime)]
  have hcfilt : ∀ m : ℕ, ∑ k ∈ Icc 0 m, c k =
      ∑ k ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt k := by
    intro m
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons, h0c, zero_add]
    have hset : (Finset.Ioc 0 m : Finset ℕ) = Finset.Icc 1 m := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by
      simp only [hc]
      by_cases h : n.Prime <;> simp [h])
  have hA : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, c k = Chebyshev.psi t - Chebyshev.theta t := by
    intro t
    rw [hcfilt ⌊t⌋₊, ← psi_sub_theta_eq_sum_nonprime ⌊t⌋₊]
    rw [show Chebyshev.psi ⌊t⌋₊ = Chebyshev.psi t from by
      rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast],
      show Chebyshev.theta ⌊t⌋₊ = Chebyshev.theta t from by
      rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]]
  have hAnonneg : ∀ t : ℝ, 0 ≤ Chebyshev.psi t - Chebyshev.theta t := by
    intro t
    have hpsi : Chebyshev.psi t = Chebyshev.psi ⌊t⌋₊ := by
      rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    have htheta : Chebyshev.theta t = Chebyshev.theta ⌊t⌋₊ := by
      rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
    rw [hpsi, htheta, psi_sub_theta_eq_sum_nonprime ⌊t⌋₊]
    exact Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hA2 : ∑ k ∈ Icc 0 ⌊(2 : ℝ)⌋₊, c k = 0 := by
    have hfl : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_ofNat 2
    rw [hfl]
    have hI : (Finset.Icc 0 2 : Finset ℕ) = {0, 1, 2} := by decide
    rw [hI]
    have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
      rintro ⟨p, k, hp, hk, hpk⟩
      have hpos : 0 < p ^ k := pow_pos (by have := hp.two_le; omega) k
      omega
    have hΛ1 : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
    have hc0 : c 0 = 0 := by simp only [hc, hΛ0]; rw [if_neg (by decide : ¬ (0:ℕ).Prime)]
    have hc1 : c 1 = 0 := by simp only [hc, hΛ1]; rw [if_neg (by decide : ¬ (1:ℕ).Prime)]
    have hc2 : c 2 = 0 := by simp only [hc]; rw [if_pos Nat.prime_two]
    rw [show ({0, 1, 2} : Finset ℕ) = insert 0 (insert 1 {2}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      hc0, hc1, hc2]
    ring
  set f : ℝ → ℝ := fun t => t⁻¹ with hf
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ f t := by
    intro t ht
    simp only [hf]
    exact differentiableAt_inv (by linarith [ht.1] : (t : ℝ) ≠ 0)
  have hderivval : ∀ t ∈ Set.Icc (2 : ℝ) x, deriv f t = -(1 / t ^ 2) := by
    intro t ht
    have ht0 : (t : ℝ) ≠ 0 := by linarith [ht.1]
    simp only [hf]
    simpa using (hasDerivAt_inv ht0).deriv
  have hIntF : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (2 : ℝ) x) := by
    simp only [hf]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : (t : ℝ) ≠ 0 := by linarith [ht.1]
    have heq : (fun s : ℝ => -(1 / s ^ 2)) =ᶠ[nhds t] deriv (fun s : ℝ => s⁻¹) := by
      filter_upwards [IsOpen.mem_nhds isOpen_ne ht0] with s hs
      simpa using ((hasDerivAt_inv hs).deriv).symm
    have hcont : ContinuousAt (fun s : ℝ => -(1 / s ^ 2)) t := by
      refine ContinuousAt.neg (ContinuousAt.div continuousAt_const ?_ (pow_ne_zero 2 ht0))
      fun_prop
    exact (hcont.congr heq).continuousWithinAt
  have habel := sum_mul_eq_sub_sub_integral_mul (c := c) (f := f) (a := 2) (b := x)
    (by norm_num) (by linarith) hdiff hIntF
  rw [Nat.floor_ofNat] at habel
  -- bound the boundary term
  have hterm1 : f x * (∑ k ∈ Icc 0 ⌊x⌋₊, c k) ≤ 4 := by
    rw [hA x]
    have hAx : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.psi_sub_theta_le (by linarith)
    have hfx : f x = 1 / x := by simp only [hf, one_div]
    rw [hfx]
    have hlog : Real.log x ≤ 2 * Real.sqrt x := by
      have h := Real.log_le_rpow_div (le_of_lt hx0) (by norm_num : (0 : ℝ) < 1 / 2)
      calc Real.log x ≤ x ^ ((1 : ℝ) / 2) / (1 / 2) := h
        _ = 2 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]; ring
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have h1 : (1 / x) * (Chebyshev.psi x - Chebyshev.theta x) ≤
        (1 / x) * (2 * Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left hAx (by positivity)
    have h2 : (1 / x) * (2 * Real.sqrt x * Real.log x) ≤
        (1 / x) * (2 * Real.sqrt x * (2 * Real.sqrt x)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [Real.sqrt_nonneg x]
    have h3 : (1 / x) * (2 * Real.sqrt x * (2 * Real.sqrt x)) = 4 := by
      have hsq : Real.sqrt x * Real.sqrt x = x := by
        rw [← pow_two, Real.sq_sqrt hx0.le]
      rw [show (2:ℝ) * Real.sqrt x * (2 * Real.sqrt x) = 4 * (Real.sqrt x * Real.sqrt x) by ring,
        hsq]
      field_simp
    exact h1.trans (h2.trans h3.le)
  -- bound the integral term in norm
  have hmaj : ∀ t ∈ Set.Ioc (2 : ℝ) x, ‖deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)‖ ≤
      2 * Real.log t / (t * Real.sqrt t) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht2' : 2 ≤ t := le_of_lt ht1
    have ht0 : (0 : ℝ) < t := by linarith
    rw [hA t, hderivval t (Set.mem_Icc.mpr ⟨ht2', ht2⟩), norm_mul]
    have hnn2 : (0:ℝ) ≤ 1 / t ^ 2 := by positivity
    have hnorm : ‖-(1 / t ^ 2)‖ = 1 / (t * t) := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hnn2, pow_two]
    rw [hnorm]
    have hnorm2 : ‖Chebyshev.psi t - Chebyshev.theta t‖ =
        Chebyshev.psi t - Chebyshev.theta t := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hAnonneg t)]
    rw [hnorm2]
    have hb : Chebyshev.psi t - Chebyshev.theta t ≤ 2 * Real.sqrt t * Real.log t :=
      Chebyshev.psi_sub_theta_le (by linarith)
    have hnn : 0 ≤ Chebyshev.psi t - Chebyshev.theta t := hAnonneg t
    have h1 : (1 / (t * t)) * (Chebyshev.psi t - Chebyshev.theta t) ≤
        (1 / (t * t)) * (2 * Real.sqrt t * Real.log t) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have heq : (1 / (t * t)) * (2 * Real.sqrt t * Real.log t) =
        2 * Real.log t / (t * Real.sqrt t) := by
      have hsq : Real.sqrt t * Real.sqrt t = t := by
        rw [← pow_two, Real.sq_sqrt ht0.le]
      have h1 : (0:ℝ) < t * t := by positivity
      have h2 : (0:ℝ) < t * Real.sqrt t := by positivity
      rw [show (1 / (t * t)) * (2 * Real.sqrt t * Real.log t) =
        (2 * Real.sqrt t * Real.log t) / (t * t) by ring]
      rw [div_eq_div_iff h1.ne' h2.ne']
      rw [show (2 * Real.sqrt t * Real.log t) * (t * Real.sqrt t)
        = 2 * Real.log t * t * (Real.sqrt t * Real.sqrt t) by ring, hsq]
      ring
    rw [heq] at h1
    exact h1
  have hmajint : IntervalIntegrable (fun t : ℝ => 2 * Real.log t / (t * Real.sqrt t))
      MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;>
      (have ht0 : (0 : ℝ) < t := by linarith [h.1, h.2])
    · apply ContinuousAt.continuousWithinAt
      fun_prop (disch := first | positivity | linarith)
    · apply ContinuousAt.continuousWithinAt
      fun_prop (disch := first | positivity | linarith)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume)
    (f := fun t : ℝ => deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k))
    (g := fun t : ℝ => 2 * Real.log t / (t * Real.sqrt t))
    (by linarith : (2 : ℝ) ≤ x) (Filter.Eventually.of_forall hmaj) hmajint
  have hint2 : ∫ t in (2 : ℝ)..x, 2 * Real.log t / (t * Real.sqrt t) ≤ 32 :=
    integral_log_div_three_halves (by norm_num) (by linarith)
  have hint3 : ‖∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)‖ ≤ 32 :=
    le_trans hbound hint2
  have hsetint : (∫ t in Set.Ioc (2 : ℝ) x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) =
      ∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  -- rewrite the target sum as the Abel left-hand side
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hunion : (Finset.Icc 1 ⌊x⌋₊ : Finset ℕ) = Finset.Icc 1 2 ∪ Ioc 2 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 2 : Finset ℕ) (Ioc 2 ⌊x⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_Ioc] at ha'
    omega
  have hsmall2 : ∑ n ∈ (Finset.Icc 1 2 : Finset ℕ),
      (if ¬ n.Prime then ArithmeticFunction.vonMangoldt n / n else 0) = 0 := by
    have hI : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
    rw [hI, Finset.sum_pair (by norm_num)]
    have h1 : ¬ (1:ℕ).Prime := by decide
    simp [h1, Nat.prime_two, ArithmeticFunction.vonMangoldt_apply_one]
  have hgoal : ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n / n = ∑ k ∈ Ioc 2 ⌊x⌋₊, c k / k := by
    rw [hunion, Finset.sum_filter, Finset.sum_union hdisj, hsmall2, zero_add]
    apply Finset.sum_congr rfl
    intro n _
    simp only [hc]
    by_cases h : n.Prime <;> simp [h]
  have hbridge : ∀ k : ℕ, c k / k = f k * c k := by
    intro k
    simp only [hf, div_eq_inv_mul]
  rw [hgoal]
  simp only [hbridge]
  rw [habel, hsetint]
  -- assemble
  have hmain : f x * (∑ k ∈ Icc 0 ⌊x⌋₊, c k) - f 2 * (∑ k ∈ Icc 0 2, c k) -
      ∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) ≤ 4 + 0 + 32 := by
    have h2 : f 2 * (∑ k ∈ Icc 0 2, c k) = 0 := by
      have : (∑ k ∈ Icc 0 2, c k) = 0 := by
        rw [← Nat.floor_ofNat (R := ℝ) 2]
        exact hA2
      rw [this, mul_zero]
    have h3 : -(∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) ≤ 32 := by
      have hnv : ‖∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)‖ =
          |∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)| :=
        Real.norm_eq_abs _
      have hna := neg_le_abs (∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k))
      linarith [hint3, hnv, hna]
    have hA1 := hterm1
    have hI1 := h3
    calc f x * (∑ k ∈ Icc 0 ⌊x⌋₊, c k) - f 2 * (∑ k ∈ Icc 0 2, c k) -
          ∫ t in (2 : ℝ)..x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)
        = f x * (∑ k ∈ Icc 0 ⌊x⌋₊, c k) + (-(∫ t in (2 : ℝ)..x,
            deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k))) := by
          rw [h2]; ring
      _ ≤ 4 + 32 := by linarith
      _ = 4 + 0 + 32 := by ring
  have hnum : (4 : ℝ) + 0 + 32 ≤ 40 := by norm_num
  exact le_trans hmain hnum

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

/-- The log-weighted prime sum twisted by a nonprincipal character mod 4 is bounded: this is
`leaf_mertens_chi4` of MertensMod4Bias.lean, from Siegel-Walfisz and the non-prime part of the
von Mangoldt sum. -/
private theorem sum_chi_log_div_prime_bound {χ : DirichletCharacter ℂ 4} (hχ : χ ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 2 ≤ x →
      ‖∑ p ∈ Nat.primesLE ⌊x⌋₊, χ (p : ZMod 4) * (Real.log p : ℂ) / p‖ ≤ B := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  obtain ⟨C, hC0, hC⟩ := sum_chi_mangoldt_div_bound hχ
  refine ⟨C + 40, by positivity, ?_⟩
  intro x hx
  have hsetP : (Nat.primesLE ⌊x⌋₊ : Finset ℕ) =
      (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Prime) := by
    ext n
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hn, hp⟩; exact ⟨⟨by have := hp.two_le; omega, hn⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨h2, hp⟩
  have hP : ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, χ (p : ZMod 4) * (Real.log p : ℂ) / p := by
    rw [hsetP]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
    push_cast
    ring
  have hN : ‖∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Prime),
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n‖ ≤ 40 := by
    refine (norm_sum_le _ _).trans ?_
    have hreal := sum_nonprime_mangoldt_div_le hx
    refine le_trans (Finset.sum_le_sum ?_) hreal
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hχ1 := DirichletCharacter.norm_le_one χ (n : ZMod 4)
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
    have hnormn : ‖((n : ℂ))‖ = (n : ℝ) := by
      rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnr]
    rw [hnormn]
    apply div_le_div_of_nonneg_right _ (le_of_lt hnr)
    calc ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod 4)‖
        ≤ ArithmeticFunction.vonMangoldt n * 1 := mul_le_mul_of_nonneg_left hχ1 hΛ
      _ = ArithmeticFunction.vonMangoldt n := by ring
  have htot := hC x hx
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n =
      (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Prime),
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n) +
        ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Prime),
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) (fun n => n.Prime) _).symm
  have hPbound : ‖∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Prime),
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n‖ ≤ C + 40 := by
    have h1 : ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Prime),
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n =
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n) -
          ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Prime),
            (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 4) / n := by
      rw [hsplit]; ring
    rw [h1]
    exact le_trans (norm_sub_le _ _) (by linarith)
  rw [← hP]
  exact hPbound


/-- `leaf_mertens_chi4` of MertensMod4Bias.lean: the log-weighted prime sum with the real
character mod 4 is bounded. -/
private theorem chi4_real_log_prime_bound {χ : DirichletCharacter ℂ 4} (hχ : χ ≠ 1)
    (hval : ∀ n : ℕ, χ (n : ZMod 4) =
      if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0) * Real.log p / p| ≤ B₀ := by
  obtain ⟨B, hB0, hB⟩ := sum_chi_log_div_prime_bound hχ
  refine ⟨B, hB0, fun x hx => ?_⟩
  have hcast : ((∑ p ∈ Nat.primesLE ⌊x⌋₊,
      (if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0) * Real.log p / p : ℝ) : ℂ) =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, χ (p : ZMod 4) * (Real.log p : ℂ) / p := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [hval p]
    by_cases hp1 : p % 4 = 1
    · rw [if_pos hp1, if_pos hp1]
      push_cast
      ring
    · by_cases hp3 : p % 4 = 3
      · rw [if_neg hp1, if_pos hp3, if_neg hp1, if_pos hp3]
        push_cast
        ring
      · rw [if_neg hp1, if_neg hp3, if_neg hp1, if_neg hp3]
        push_cast
        ring
  have hre : ∑ p ∈ Nat.primesLE ⌊x⌋₊,
      (if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0) * Real.log p / p =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, χ (p : ZMod 4) * (Real.log p : ℂ) / p).re := by
    have := congrArg Complex.re hcast
    rw [Complex.ofReal_re] at this
    exact this
  rw [hre]
  exact le_trans (Complex.abs_re_le_norm _) (hB x hx)


/-- Abel summation for the sum of chi p / p over a block of primes, for any weight chi; the weighted
form of abel_recip in AlmostPrimes/Decomp1528b. Inlined from MertensMod4Bias.lean. -/
private theorem abel_weighted (χ : ℕ → ℝ) {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime,
        χ p / p =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊,
          χ p * log p / p) / log x -
        (∑ p ∈ Nat.primesLE ⌊y⌋₊,
          χ p * log p / p) / log y +
        ∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊,
          χ p * log p / p) /
            (t * log t ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then χ n * log n / n else 0
  let f : ℝ → ℝ := fun t => (log t)⁻¹
  have hs (t : ℝ) : (∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      ∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p := by
    simp only [c, ← sum_filter]
    congr 1
    ext k
    simp [Nat.mem_primesLE]
  have hd (t : ℝ) (ht : 1 < t) : HasDerivAt f (-(1 / (t * log t ^ 2))) t := by
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (Real.log_pos ht).ne'
    convert (Real.hasDerivAt_log ht0).inv hl using 1
    field_simp
  have hc : ContinuousOn (fun t : ℝ => -(1 / (t * log t ^ 2))) (Set.Icc y x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y x) := by
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (hd t (by linarith [ht.1])).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c (by linarith : 0 ≤ y) hyx
    (fun t ht => (hd t (by linarith [ht.1])).differentiableAt) hi
  have hleft : (∑ k ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, f k * c k) =
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, χ p / p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    dsimp [f, c]
    split_ifs with hp
    · have hl : log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      field_simp
    · simp
  have hI : (∫ t in Set.Ioc y x, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -(∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p) / (t * log t ^ 2)) := by
    rw [← intervalIntegral.integral_of_le hyx, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hyx] at ht
    change deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -((∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p) / (t * log t ^ 2))
    rw [(hd t (by linarith [ht.1])).deriv, hs]
    ring
  rw [hleft, hs, hs, hI] at h
  simpa [f, div_eq_mul_inv, mul_comm, sub_neg_eq_add] using h


/-- The bias of the sums of 1/p between the classes 1 and 3 mod 4 is bounded, by Abel summation
from chi4_real_log_prime_bound. Inlined from MertensMod4Bias.lean. -/
private theorem chi4_bias_bound {χ : DirichletCharacter ℂ 4} (hχ : χ ≠ 1)
    (hval : ∀ n : ℕ, χ (n : ZMod 4) =
      if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y x : ℝ, 2 ≤ y → y ≤ x →
      ∑ p ∈ ((Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).filter (fun p => p % 4 = 1), (1 : ℝ) / p -
        ∑ p ∈ ((Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).filter (fun p => p % 4 = 3), (1 : ℝ) / p ≤ B := by
  obtain ⟨B₀, hB₀, H⟩ := chi4_real_log_prime_bound (χ := χ) hχ hval
  refine ⟨4 * B₀, by positivity, ?_⟩
  intro y x hy hyx
  set ψ4 : ℕ → ℝ := fun p => if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0 with hψ4
  set F := (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime
  have heq : ∑ p ∈ F.filter (fun p => p % 4 = 1), (1 : ℝ) / p -
      ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p = ∑ p ∈ F, ψ4 p / p := by
    rw [Finset.sum_filter (s := F), Finset.sum_filter (s := F), ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    simp only [hψ4]
    split_ifs with h1 h3 <;> first | omega | ring
  rw [heq, abel_weighted ψ4 hy hyx]
  have hx2 : 2 ≤ x := hy.trans hyx
  have hl2 : (1 / 2 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hly : 1 / 2 < log y := lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) hy)
  have hlx : 1 / 2 < log x := lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) hx2)
  have hlyp : 0 < log y := by linarith
  have hlxp : 0 < log x := by linarith
  set Bf : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, ψ4 p * log p / p with hBf
  let w : ℝ → ℝ := fun t => 1 / (t * log t ^ 2)
  have hwi : IntervalIntegrable w MeasureTheory.volume y x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hyx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
    apply ContinuousAt.continuousWithinAt
    dsimp [w]
    fun_prop (disch := assumption)
  have hint : (∫ t in y..x, w t) = 1 / log y - 1 / log x := by
    have hd : ∀ t ∈ Set.uIcc y x,
        HasDerivAt (fun t : ℝ => -(log t)⁻¹) (w t) t := by
      intro t ht
      rw [Set.uIcc_of_le hyx] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      convert ((Real.hasDerivAt_log ht0).inv hl).neg using 1
      dsimp [w]
      field_simp
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hwi
    simpa only [one_div, neg_sub_neg] using hi
  have hbound : |∫ t in y..x, Bf t / (t * log t ^ 2)| ≤ ∫ t in y..x, B₀ * w t := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
      (f := fun t => Bf t / (t * log t ^ 2)) hyx
      (g := fun t => B₀ * w t) (Filter.Eventually.of_forall (fun t ht => by
        have ht2 : 2 ≤ t := le_trans hy ht.1.le
        have hden : 0 < t * log t ^ 2 := by
          have hlog := Real.log_pos (by linarith : 1 < t)
          positivity
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
        have h := H t ht2
        exact (div_le_div_of_nonneg_right h hden.le).trans_eq (by dsimp [w]; ring)))
      (hwi.const_mul B₀)
    exact hb
  rw [intervalIntegral.integral_const_mul, hint] at hbound
  have hBx := H x hx2
  have hBy := H y hy
  have h1 : Bf x / log x ≤ B₀ / log x := by
    rw [div_le_div_iff_of_pos_right hlxp]; exact (le_abs_self _).trans hBx
  have h2 : -(Bf y / log y) ≤ B₀ / log y := by
    rw [← neg_div, div_le_div_iff_of_pos_right hlyp]; exact (neg_le_abs _).trans hBy
  have h3 : (∫ t in y..x, Bf t / (t * log t ^ 2)) ≤ B₀ * (1 / log y - 1 / log x) :=
    (le_abs_self _).trans hbound
  have hiy : 1 / log y ≤ 2 := by rw [div_le_iff₀ hlyp]; linarith
  have hmain : Bf x / log x - Bf y / log y + ∫ t in y..x, Bf t / (t * log t ^ 2) ≤
      2 * B₀ * (1 / log y) := by
    have : B₀ / log x + B₀ / log y + B₀ * (1 / log y - 1 / log x) = 2 * B₀ * (1 / log y) := by
      ring
    linarith
  calc _ ≤ 2 * B₀ * (1 / log y) := hmain
    _ ≤ 2 * B₀ * 2 := mul_le_mul_of_nonneg_left hiy (by positivity)
    _ = 4 * B₀ := by ring


/-- Each local factor of the Euler product is at least the exponential of omega p / p, since
1 - x is at most exp of -x. Inlined from MertensMod4Split.lean. -/
private theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  rw [le_inv_comm₀ (Real.exp_pos x) h1, ← Real.exp_neg]
  exact h2

/-- Page 15: the product is at least exp of the sum of omega p / p, which is the sum of 1/p plus
the sum over p = 3 mod 4 of 1/p, then mertens2_block and the bias bound. Inlined from
MertensMod4Split.lean. -/
private theorem product_ge_log_ratio_aux {χ : DirichletCharacter ℂ 4} (hχ : χ ≠ 1)
    (hval : ∀ n : ℕ, χ (n : ZMod 4) =
      if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤
        C * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  obtain ⟨B, hB0, HB⟩ := chi4_bias_bound (χ := χ) hχ hval
  refine ⟨Real.exp (6 + B / 2), Real.exp_pos _, ?_⟩
  intro w hw z hz1
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogw1 : 1 ≤ Real.log w := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set F := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z) with hF
  -- facts about primes in F
  have hFp : ∀ p ∈ F, p.Prime ∧ w < p ∧ (10 : ℝ) < p := by
    intro p hp
    have h := (mem_filter.mp hp).2
    exact ⟨h.1, h.2.1, lt_of_le_of_lt hw10 (by exact_mod_cast h.2.1)⟩
  have hx : ∀ p ∈ F, (envelopingOmega w p : ℝ) / p < 1 := by
    intro p hp
    obtain ⟨-, -, h10⟩ := hFp p hp
    have hω : (envelopingOmega w p : ℝ) ≤ 2 := by
      unfold envelopingOmega; split_ifs <;> norm_num
    rw [div_lt_one (by linarith)]; linarith
  have hfac1 : ∀ p ∈ F, 1 ≤ (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    intro p hp
    have h0 : 0 ≤ (envelopingOmega w p : ℝ) / p := by positivity
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp ((envelopingOmega w p : ℝ) / p) := Real.exp_le_exp.mpr h0
      _ ≤ _ := exp_le_inv_one_sub (hx p hp)
  have hP1 : 1 ≤ ∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := one_le_prod₀ hfac1
  have hexpP : Real.exp (∑ p ∈ F, (envelopingOmega w p : ℝ) / p) ≤
      ∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => exp_le_inv_one_sub (hx p hp))
  by_cases hzw : z < w
  · -- below w the ratio is below one and the product is at least one
    have hlz : 0 ≤ Real.log z := Real.log_nonneg hz1
    have hratio : Real.log z / Real.log w ≤ 1 := by
      rw [div_le_one hlogw]
      exact Real.log_le_log (by linarith) hzw.le
    have hr : (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one (div_nonneg hlz hlogw.le) hratio (by norm_num)
    have hC1 : 1 ≤ Real.exp (6 + B / 2) := Real.one_le_exp (by positivity)
    calc _ ≤ 1 := hr
      _ ≤ Real.exp (6 + B / 2) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hP1 (Real.exp_pos _).le
  · push_neg at hzw
    have hz10 : (10 : ℝ) ≤ z := hw10.trans hzw
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    -- F is the block of primes in mertens2_block
    have hFeq : F = (Ioc ⌊(w : ℝ)⌋₊ ⌊z⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast]
      ext p
      simp only [hF, mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨-, hp, hwp, hpz⟩
        exact ⟨⟨hwp, Nat.le_floor hpz⟩, hp⟩
      · rintro ⟨⟨hwp, hpz⟩, hp⟩
        refine ⟨by omega, hp, hwp, ?_⟩
        exact (Nat.le_floor_iff (by linarith)).mp hpz
    have hM := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block (y := (w : ℝ)) (x := z) (le_trans (by norm_num) hw10) hzw
    rw [← hFeq] at hM
    have hS1 : Real.log (Real.log z) - Real.log (Real.log w) - 4 / Real.log w ≤
        ∑ p ∈ F, (1 : ℝ) / p := by
      have := (abs_le.mp hM).1; linarith
    have hbias := HB w z (le_trans (by norm_num) hw10) hzw
    rw [← hFeq] at hbias
    -- split the sum of 1/p by residue mod 4
    have hodd : ∀ p ∈ F, p % 4 = 1 ∨ p % 4 = 3 := by
      intro p hp
      obtain ⟨hpp, -, h10⟩ := hFp p hp
      have hne : p ≠ 2 := by
        intro h; rw [h] at h10; norm_num at h10
      have := hpp.eq_one_or_self_of_dvd 2
      rcases Nat.even_or_odd p with he | ho
      · exact absurd (this (even_iff_two_dvd.mp he)) (by omega)
      · have := Nat.odd_iff.mp ho; omega
    have hsplit : ∑ p ∈ F, (1 : ℝ) / p =
        ∑ p ∈ F.filter (fun p => p % 4 = 1), (1 : ℝ) / p +
          ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p := by
      rw [← sum_filter_add_sum_filter_not F (fun p => p % 4 = 1)]
      congr 1
      apply sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨hp, h⟩; exact ⟨hp, by rcases hodd p hp with h' | h' <;> omega⟩
      · rintro ⟨hp, h⟩; exact ⟨hp, by omega⟩
    have hω : ∑ p ∈ F, (envelopingOmega w p : ℝ) / p =
        ∑ p ∈ F, (1 : ℝ) / p + ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p := by
      rw [Finset.sum_filter (s := F) (fun p => p % 4 = 3), ← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      obtain ⟨-, hwp, -⟩ := hFp p hp
      unfold envelopingOmega
      rw [if_neg (by omega)]
      rcases hodd p hp with h | h
      · rw [if_pos h, if_neg (by omega)]; push_cast; ring
      · rw [if_neg (by omega), if_pos h]; push_cast; ring
    have hsum : (3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)) - (6 + B / 2) ≤
        ∑ p ∈ F, (envelopingOmega w p : ℝ) / p := by
      have h4 : 4 / Real.log w ≤ 4 := by
        rw [div_le_iff₀ hlogw]; linarith
      rw [hω]; linarith
    have hratio : (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) =
        Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w))) := by
      rw [Real.rpow_def_of_pos (div_pos hlogz hlogw), Real.log_div hlogz.ne' hlogw.ne']
      ring_nf
    rw [hratio]
    calc Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)))
        = Real.exp (6 + B / 2) *
            Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)) - (6 + B / 2)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (6 + B / 2) * Real.exp (∑ p ∈ F, (envelopingOmega w p : ℝ) / p) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexpP (Real.exp_pos _).le


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
  obtain ⟨χ, hχ, -, -, hval⟩ := chi4_exists
  exact product_ge_log_ratio_aux (χ := χ) hχ hval

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
