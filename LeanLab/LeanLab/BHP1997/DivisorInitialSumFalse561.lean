/-
DivisorInitialSumFalse561

AI wrote this Lean code. The binary Goldbach conjecture is OPEN; nothing here changes that.

This file refutes the sorry leaf `leaf_divisor_initial_sum561` of
`LeanLab/BHP1997/SPLIT_leaf_coefficient_energies561.lean`.  The leaf claims, for every real `B`,
a bound `∑_{Y < k ≤ 2Y} d(k)^(2B) ≤ K * Y * (log x)^(2|B|+4)`.  At `B = 5` the left side is a
tenth moment of the divisor function, which is at least `c * Y * (log Y)^15` by the elementary
bound `∑_{N < k ≤ 2N} d(k)^2 ≥ (N/4) * H_z^3` (with `N = z^3`) and the power mean inequality,
while the right side with `x = 2Y` is only `K * Y * (log 2Y)^14`.

Only `import Mathlib`; no new definitions, no axioms beyond the three standard ones.
-/
import Mathlib

namespace LeanLab.BHP1997.DivisorInitialSumFalse561

open Finset

/-- Standard fact: for `1 ≤ m ≤ N` the interval `(N, 2N]` holds at least `N / (2m)` multiples
of `m`. -/
theorem card_multiples_Ioc_ge (N m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    (N : ℝ) / (2 * m) ≤ (((Ioc N (2 * N)).filter (fun k => m ∣ k)).card : ℝ) := by
  have hq : 1 ≤ N / m := Nat.div_pos hmN hm
  have h1 : N < m * (N / m + 1) := Nat.lt_mul_div_succ N hm
  have h2 : m * (N / m) ≤ N := Nat.mul_div_le N m
  have hcard : N / m ≤ ((Ioc N (2 * N)).filter (fun k => m ∣ k)).card := by
    have hc : (Ioc (N / m) (2 * (N / m))).card = N / m := by
      rw [Nat.card_Ioc]; omega
    rw [← hc]
    apply card_le_card_of_injOn (fun t => m * t)
    · intro t ht
      simp only [coe_Ioc, Set.mem_Ioc] at ht
      simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
      refine ⟨⟨?_, ?_⟩, Dvd.intro t rfl⟩
      · calc N < m * (N / m + 1) := h1
          _ ≤ m * t := Nat.mul_le_mul_left m ht.1
      · calc m * t ≤ m * (2 * (N / m)) := Nat.mul_le_mul_left m ht.2
          _ = 2 * (m * (N / m)) := by ring
          _ ≤ 2 * N := Nat.mul_le_mul_left 2 h2
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hm hab
  have hmR : (0 : ℝ) < 2 * (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have h3 : N ≤ (N / m) * (2 * m) := by
    have : m * (N / m + 1) ≤ m * (2 * (N / m)) := Nat.mul_le_mul_left m (by omega)
    calc N ≤ m * (2 * (N / m)) := by omega
      _ = (N / m) * (2 * m) := by ring
  have h4 : (N : ℝ) / (2 * m) ≤ ((N / m : ℕ) : ℝ) := by
    rw [div_le_iff₀ hmR]
    exact_mod_cast h3
  exact h4.trans (by exact_mod_cast hcard)

/-- Standard fact: `d(k)^2` is at least the number of triples `(g, a, b)` with `a, b` coprime and
`g * a * b ∣ k`, through the injection `(g, a, b) ↦ (g * a, g * b)` into pairs of divisors. -/
theorem card_coprime_triples_le (z k : ℕ) (hk : k ≠ 0) :
    ((Icc 1 z ×ˢ ((Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2))).filter
        (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ k)).card ≤ k.divisors.card ^ 2 := by
  rw [sq, ← card_product]
  apply card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => (t.1 * t.2.1, t.1 * t.2.2))
  · rintro ⟨g, a, b⟩ ht
    simp only [coe_filter, mem_product, mem_Icc, mem_filter, Set.mem_ofPred_eq] at ht
    simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors]
    obtain ⟨_, hd⟩ := ht
    exact ⟨⟨(Dvd.intro b rfl).trans hd, hk⟩, ⟨Dvd.dvd.trans (show g * b ∣ g * a * b from ⟨a, by ring⟩) hd, hk⟩⟩
  · rintro ⟨g, a, b⟩ ht ⟨g', a', b'⟩ ht' heq
    simp only [coe_filter, mem_product, mem_Icc, mem_filter, Set.mem_ofPred_eq] at ht ht'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hc : Nat.gcd a b = 1 := ht.1.2.2
    have hc' : Nat.gcd a' b' = 1 := ht'.1.2.2
    have hg : g = g' := by
      have e1 : Nat.gcd (g * a) (g * b) = g := by rw [Nat.gcd_mul_left, hc, mul_one]
      have e2 : Nat.gcd (g' * a') (g' * b') = g' := by rw [Nat.gcd_mul_left, hc', mul_one]
      rw [← e1, ← e2, h1, h2]
    subst hg
    have hgpos : 0 < g := ht.1.1.1
    have ha : a = a' := Nat.eq_of_mul_eq_mul_left hgpos h1
    have hb : b = b' := Nat.eq_of_mul_eq_mul_left hgpos h2
    rw [ha, hb]

/-- Standard fact (swap of summation): for `z^3 ≤ N`,
`∑_{N < k ≤ 2N} d(k)^2 ≥ (N/2) * H_z * T_z`, where `H_z = ∑_{g ≤ z} 1/g` and `T_z` is the sum of
`1/(a b)` over coprime pairs `a, b ≤ z`. -/
theorem sum_card_sq_ge (z N : ℕ) (hN : z ^ 3 ≤ N) :
    (N : ℝ) / 2 * ((∑ g ∈ Icc 1 z, (g : ℝ)⁻¹) *
        ∑ p ∈ (Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2),
          ((p.1 : ℝ) * p.2)⁻¹) ≤
      ∑ k ∈ Ioc N (2 * N), ((k.divisors.card : ℕ) : ℝ) ^ 2 := by
  set Tr : Finset (ℕ × ℕ × ℕ) :=
    Icc 1 z ×ˢ ((Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)) with hTr
  have hB : ∀ k ∈ Ioc N (2 * N),
      ((Tr.filter (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ k)).card : ℝ) ≤
        ((k.divisors.card : ℕ) : ℝ) ^ 2 := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have := (mem_Ioc.mp hk).1
      omega
    have := card_coprime_triples_le z k hk0
    exact_mod_cast this
  have hA : ∀ t ∈ Tr, (N : ℝ) / (2 * ((t.1 * t.2.1 * t.2.2 : ℕ) : ℝ)) ≤
      (((Ioc N (2 * N)).filter (fun k => t.1 * t.2.1 * t.2.2 ∣ k)).card : ℝ) := by
    rintro ⟨g, a, b⟩ ht
    simp only [hTr, mem_product, mem_Icc, mem_filter] at ht
    obtain ⟨⟨hg1, hg2⟩, ⟨⟨ha1, ha2⟩, hb1, hb2⟩, _⟩ := ht
    apply card_multiples_Ioc_ge
    · exact Nat.mul_pos (Nat.mul_pos hg1 ha1) hb1
    · calc g * a * b ≤ z * z * z := Nat.mul_le_mul (Nat.mul_le_mul hg2 ha2) hb2
        _ = z ^ 3 := by ring
        _ ≤ N := hN
  calc (N : ℝ) / 2 * ((∑ g ∈ Icc 1 z, (g : ℝ)⁻¹) *
        ∑ p ∈ (Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2),
          ((p.1 : ℝ) * p.2)⁻¹)
      = ∑ t ∈ Tr, (N : ℝ) / (2 * ((t.1 * t.2.1 * t.2.2 : ℕ) : ℝ)) := by
        rw [sum_mul_sum, ← sum_product', mul_sum]
        apply sum_congr rfl
        intro t _
        push_cast
        ring
    _ ≤ ∑ t ∈ Tr, (((Ioc N (2 * N)).filter (fun k => t.1 * t.2.1 * t.2.2 ∣ k)).card : ℝ) :=
        sum_le_sum hA
    _ = ∑ k ∈ Ioc N (2 * N),
          ((Tr.filter (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ k)).card : ℝ) := by
        simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        exact sum_comm
    _ ≤ ∑ k ∈ Ioc N (2 * N), ((k.divisors.card : ℕ) : ℝ) ^ 2 := sum_le_sum hB

/-- Standard fact: `∑_{h ≤ z} 1/h^2 ≤ 2`. -/
theorem sum_inv_sq_le_two (z : ℕ) : ∑ h ∈ Icc 1 z, ((h : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (z + 1)
  have e : Ioo 0 (z + 1) = Icc 1 z := by
    ext k; simp only [mem_Ioo, mem_Icc]; omega
  rw [e] at h
  simpa using h

/-- Standard fact: `H_z^2 ≤ 2 * T_z`, since every pair `(a', b')` with entries at most `z` is
uniquely `(h a, h b)` with `h = gcd(a', b')` and `a, b` coprime, and `∑ 1/h^2 ≤ 2`. -/
theorem harmonic_sq_le (z : ℕ) :
    (∑ a ∈ Icc 1 z, (a : ℝ)⁻¹) ^ 2 ≤
      2 * ∑ p ∈ (Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2),
          ((p.1 : ℝ) * p.2)⁻¹ := by
  have hφ : ∀ q ∈ Icc 1 z ×ˢ Icc 1 z,
      (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ =
        (((Nat.gcd q.1 q.2 : ℕ) : ℝ) ^ 2)⁻¹ *
          (((q.1 / Nat.gcd q.1 q.2 : ℕ) : ℝ) * ((q.2 / Nat.gcd q.1 q.2 : ℕ) : ℝ))⁻¹ := by
    rintro ⟨a, b⟩ _
    have e1 : (a : ℝ) = ((Nat.gcd a b : ℕ) : ℝ) * ((a / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have e2 : (b : ℝ) = ((Nat.gcd a b : ℕ) : ℝ) * ((b / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    simp only
    conv_lhs => rw [e1, e2]
    ring
  have hT0 : ∀ t ∈ Icc 1 z ×ˢ
      ((Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)),
      (0 : ℝ) ≤ ((t.1 : ℝ) ^ 2)⁻¹ * ((t.2.1 : ℝ) * t.2.2)⁻¹ := by
    intro t _
    positivity
  calc (∑ a ∈ Icc 1 z, (a : ℝ)⁻¹) ^ 2
      = ∑ q ∈ Icc 1 z ×ˢ Icc 1 z, (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ := by
        rw [sq, sum_mul_sum, ← sum_product']
    _ = ∑ q ∈ Icc 1 z ×ˢ Icc 1 z,
          (fun t : ℕ × ℕ × ℕ => ((t.1 : ℝ) ^ 2)⁻¹ * ((t.2.1 : ℝ) * t.2.2)⁻¹)
            (Nat.gcd q.1 q.2, q.1 / Nat.gcd q.1 q.2, q.2 / Nat.gcd q.1 q.2) :=
        sum_congr rfl hφ
    _ = ∑ t ∈ (Icc 1 z ×ˢ Icc 1 z).image
            (fun q : ℕ × ℕ => (Nat.gcd q.1 q.2, q.1 / Nat.gcd q.1 q.2, q.2 / Nat.gcd q.1 q.2)),
          ((t.1 : ℝ) ^ 2)⁻¹ * ((t.2.1 : ℝ) * t.2.2)⁻¹ := by
        rw [sum_image]
        rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hg, ha, hb⟩ := heq
        have ea : a = Nat.gcd a b * (a / Nat.gcd a b) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
        have eb : b = Nat.gcd a b * (b / Nat.gcd a b) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
        have ea' : a' = Nat.gcd a' b' * (a' / Nat.gcd a' b') :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left a' b')).symm
        have eb' : b' = Nat.gcd a' b' * (b' / Nat.gcd a' b') :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right a' b')).symm
        have h1 : a = a' := by
          calc a = Nat.gcd a b * (a / Nat.gcd a b) := ea
            _ = Nat.gcd a' b' * (a' / Nat.gcd a' b') := by rw [ha, hg]
            _ = a' := ea'.symm
        have h2 : b = b' := by
          calc b = Nat.gcd a b * (b / Nat.gcd a b) := eb
            _ = Nat.gcd a' b' * (b' / Nat.gcd a' b') := by rw [hb, hg]
            _ = b' := eb'.symm
        rw [h1, h2]
    _ ≤ ∑ t ∈ Icc 1 z ×ˢ
            ((Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)),
          ((t.1 : ℝ) ^ 2)⁻¹ * ((t.2.1 : ℝ) * t.2.2)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro t ht
          simp only [mem_image, mem_product, mem_Icc] at ht
          obtain ⟨⟨a, b⟩, ⟨⟨ha1, ha2⟩, hb1, hb2⟩, rfl⟩ := ht
          have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha1
          have hga : Nat.gcd a b ≤ a := Nat.gcd_le_left b ha1
          have hgb : Nat.gcd a b ≤ b := Nat.gcd_le_right a hb1
          simp only [mem_product, mem_Icc, mem_filter]
          refine ⟨⟨hgpos, hga.trans ha2⟩,
            ⟨⟨Nat.div_pos hga hgpos, (Nat.div_le_self _ _).trans ha2⟩,
              Nat.div_pos hgb hgpos, (Nat.div_le_self _ _).trans hb2⟩,
            Nat.coprime_div_gcd_div_gcd hgpos⟩
        · intro t ht _
          exact hT0 t ht
    _ = (∑ h ∈ Icc 1 z, ((h : ℝ) ^ 2)⁻¹) *
          ∑ p ∈ (Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2),
            ((p.1 : ℝ) * p.2)⁻¹ := by
        rw [sum_mul_sum, ← sum_product']
    _ ≤ 2 * ∑ p ∈ (Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2),
            ((p.1 : ℝ) * p.2)⁻¹ := by
        apply mul_le_mul_of_nonneg_right (sum_inv_sq_le_two z)
        apply sum_nonneg
        intro p _
        positivity

/-- Standard fact: `log (z + 1) ≤ H_z`, the harmonic sum written over `Icc 1 z`. -/
theorem log_le_harmonic_Icc (z : ℕ) :
    Real.log ((z : ℝ) + 1) ≤ ∑ a ∈ Icc 1 z, (a : ℝ)⁻¹ := by
  have h := log_add_one_le_harmonic z
  rw [harmonic_eq_sum_Icc] at h
  simpa using h

/-- Standard fact (second moment of the divisor function, lower bound): with `N = z^3`,
`∑_{N < k ≤ 2N} d(k)^2 ≥ (N/4) * (log (z+1))^3`. -/
theorem sum_card_sq_ge_log (z : ℕ) :
    ((z ^ 3 : ℕ) : ℝ) / 4 * Real.log ((z : ℝ) + 1) ^ 3 ≤
      ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 2 := by
  have h1 := sum_card_sq_ge z (z ^ 3) le_rfl
  have h2 := harmonic_sq_le z
  have h3 := log_le_harmonic_Icc z
  have hL : 0 ≤ Real.log ((z : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
    linarith)
  set H := ∑ a ∈ Icc 1 z, (a : ℝ)⁻¹ with hH
  set T := ∑ p ∈ (Icc 1 z ×ˢ Icc 1 z).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2),
    ((p.1 : ℝ) * p.2)⁻¹ with hT
  set L := Real.log ((z : ℝ) + 1) with hLdef
  have hH0 : 0 ≤ H := hL.trans h3
  have hN0 : (0 : ℝ) ≤ ((z ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : L ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ hL h3 3
  have h5 : H ^ 3 ≤ 2 * (H * T) := by
    calc H ^ 3 = H * H ^ 2 := by ring
      _ ≤ H * (2 * T) := mul_le_mul_of_nonneg_left h2 hH0
      _ = 2 * (H * T) := by ring
  calc ((z ^ 3 : ℕ) : ℝ) / 4 * L ^ 3 ≤ ((z ^ 3 : ℕ) : ℝ) / 4 * (2 * (H * T)) :=
        mul_le_mul_of_nonneg_left (h4.trans h5) (by positivity)
    _ = ((z ^ 3 : ℕ) : ℝ) / 2 * (H * T) := by ring
    _ ≤ _ := h1

/-- Standard fact (tenth moment of the divisor function, lower bound, by the power mean
inequality): with `N = z^3`, `N * (log (z+1))^15 ≤ 4^5 * ∑_{N < k ≤ 2N} d(k)^10`. -/
theorem sum_card_pow_ten_ge_log (z : ℕ) (hz : 1 ≤ z) :
    ((z ^ 3 : ℕ) : ℝ) * Real.log ((z : ℝ) + 1) ^ 15 ≤
      4 ^ 5 * ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 10 := by
  have h1 := sum_card_sq_ge_log z
  have hL : 0 ≤ Real.log ((z : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
    linarith)
  have hNpos : (0 : ℝ) < ((z ^ 3 : ℕ) : ℝ) := by
    have : 0 < z ^ 3 := Nat.pow_pos hz
    exact_mod_cast this
  have hpm := pow_sum_div_card_le_sum_pow (s := Ioc (z ^ 3) (2 * z ^ 3))
    (f := fun k : ℕ => ((k.divisors.card : ℕ) : ℝ) ^ 2) (fun i _ => by positivity) 4
  have hcard : ((Ioc (z ^ 3) (2 * z ^ 3)).card : ℝ) = ((z ^ 3 : ℕ) : ℝ) := by
    rw [Nat.card_Ioc]
    congr 1
    omega
  rw [hcard] at hpm
  simp only [Nat.reduceAdd] at hpm
  have hpm' : (∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 2) ^ 5 /
      ((z ^ 3 : ℕ) : ℝ) ^ 4 ≤ ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 10 := by
    refine hpm.trans (le_of_eq ?_)
    apply sum_congr rfl
    intro k _
    ring
  set S2 := ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 2 with hS2
  set S10 := ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 10 with hS10
  set L := Real.log ((z : ℝ) + 1) with hLdef
  set N := ((z ^ 3 : ℕ) : ℝ) with hNdef
  have h2 : (N / 4 * L ^ 3) ^ 5 ≤ S2 ^ 5 := pow_le_pow_left₀ (by positivity) h1 5
  rw [div_le_iff₀ (by positivity)] at hpm'
  have h3 : N ^ 4 * (N * L ^ 15) ≤ N ^ 4 * (4 ^ 5 * S10) := by
    calc N ^ 4 * (N * L ^ 15) = 4 ^ 5 * (N / 4 * L ^ 3) ^ 5 := by ring
      _ ≤ 4 ^ 5 * S2 ^ 5 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 4 ^ 5 * (S10 * N ^ 4) := mul_le_mul_of_nonneg_left hpm' (by positivity)
      _ = N ^ 4 * (4 ^ 5 * S10) := by ring
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- The leaf `leaf_divisor_initial_sum561` is false at `B = 5`: the tenth moment of the divisor
function over `(Y, 2Y]` exceeds `K * Y * (log 2Y)^14` for large `Y`. -/
theorem leaf_divisor_initial_sum561_false_at_five :
    ¬ ∃ K : ℝ, 1 ≤ K ∧ ∀ Y x : ℝ, 1 ≤ Y → 2 * Y ≤ x →
      ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, (((k.divisors.card : ℕ) : ℝ) ^ (5 : ℝ)) ^ 2 ≤
        K * Y * Real.log x ^ (2 * |(5 : ℝ)| + 4) := by
  rintro ⟨K, hK, h⟩
  -- choose `z` with `log (z + 1) > 4^5 * 4^14 * K`
  set M : ℝ := 4 ^ 5 * 4 ^ 14 * K with hM
  set z : ℕ := ⌈Real.exp M⌉₊ with hzdef
  have hz_ge : Real.exp M ≤ (z : ℝ) := Nat.le_ceil _
  have hz1 : 1 ≤ z := by
    have : (0 : ℝ) < (z : ℝ) := (Real.exp_pos M).trans_le hz_ge
    exact_mod_cast this
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  set L := Real.log ((z : ℝ) + 1) with hLdef
  have hLM : M < L := by
    have : Real.exp M < (z : ℝ) + 1 := by linarith
    calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
      _ < L := Real.log_lt_log (Real.exp_pos M) this
  have hMpos : 0 < M := by
    have hK0 : 0 < K := by linarith
    rw [hM]; positivity
  have hLpos : 0 < L := hMpos.trans hLM
  have hNpos : (0 : ℝ) < ((z ^ 3 : ℕ) : ℝ) := by
    have : 0 < z ^ 3 := Nat.pow_pos hz1
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ ((z ^ 3 : ℕ) : ℝ) := by
    have : 1 ≤ z ^ 3 := Nat.pow_pos hz1
    exact_mod_cast this
  have hspec := h ((z ^ 3 : ℕ) : ℝ) (2 * ((z ^ 3 : ℕ) : ℝ)) hN1 le_rfl
  have hfl1 : ⌊((z ^ 3 : ℕ) : ℝ)⌋₊ = z ^ 3 := Nat.floor_natCast _
  have hfl2 : ⌊2 * ((z ^ 3 : ℕ) : ℝ)⌋₊ = 2 * z ^ 3 := by
    have : 2 * ((z ^ 3 : ℕ) : ℝ) = ((2 * z ^ 3 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.floor_natCast]
  rw [hfl1, hfl2] at hspec
  have hexp : (2 * |(5 : ℝ)| + 4 : ℝ) = ((14 : ℕ) : ℝ) := by
    rw [abs_of_nonneg (by norm_num)]; norm_num
  rw [hexp, Real.rpow_natCast] at hspec
  have hsum : ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), (((k.divisors.card : ℕ) : ℝ) ^ (5 : ℝ)) ^ 2 =
      ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 10 := by
    apply sum_congr rfl
    intro k _
    have : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast, ← pow_mul]
  rw [hsum] at hspec
  have hlow := sum_card_pow_ten_ge_log z hz1
  -- `log (2 z^3) ≤ 4 * log (z + 1)`
  have hlog : Real.log (2 * ((z ^ 3 : ℕ) : ℝ)) ≤ 4 * L := by
    have h1 : 2 * ((z ^ 3 : ℕ) : ℝ) ≤ ((z : ℝ) + 1) ^ 4 := by
      push_cast
      have h3 : (z : ℝ) ^ 3 ≤ ((z : ℝ) + 1) ^ 3 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 3
      have h4 : (0 : ℝ) ≤ ((z : ℝ) + 1) ^ 3 := by positivity
      nlinarith
    calc Real.log (2 * ((z ^ 3 : ℕ) : ℝ)) ≤ Real.log (((z : ℝ) + 1) ^ 4) :=
          Real.log_le_log (by positivity) h1
      _ = 4 * L := by rw [Real.log_pow, hLdef]; norm_num
  have hlog0 : 0 ≤ Real.log (2 * ((z ^ 3 : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
  have hpow : Real.log (2 * ((z ^ 3 : ℕ) : ℝ)) ^ 14 ≤ (4 * L) ^ 14 :=
    pow_le_pow_left₀ hlog0 hlog 14
  set N := ((z ^ 3 : ℕ) : ℝ) with hNdef
  have hKpos : 0 < K := by linarith
  have hchain : N * L ^ 15 ≤ N * L ^ 14 * M := by
    calc N * L ^ 15 ≤ 4 ^ 5 * ∑ k ∈ Ioc (z ^ 3) (2 * z ^ 3), ((k.divisors.card : ℕ) : ℝ) ^ 10 :=
          hlow
      _ ≤ 4 ^ 5 * (K * N * Real.log (2 * N) ^ 14) :=
          mul_le_mul_of_nonneg_left hspec (by positivity)
      _ ≤ 4 ^ 5 * (K * N * (4 * L) ^ 14) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = N * L ^ 14 * M := by rw [hM]; ring
  have hpos : 0 < N * L ^ 14 := by positivity
  have : L ≤ M := by
    have h' : N * L ^ 14 * L ≤ N * L ^ 14 * M := by
      calc N * L ^ 14 * L = N * L ^ 15 := by ring
        _ ≤ _ := hchain
    exact le_of_mul_le_mul_left h' hpos
  linarith

/-- The leaf `leaf_divisor_initial_sum561`, as stated for all real `B`, is false. -/
theorem leaf_divisor_initial_sum561_false :
    ¬ ∀ B : ℝ, ∃ K : ℝ, 1 ≤ K ∧ ∀ Y x : ℝ, 1 ≤ Y → 2 * Y ≤ x →
      ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, (((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 ≤
        K * Y * Real.log x ^ (2 * |B| + 4) := fun h =>
  leaf_divisor_initial_sum561_false_at_five (h 5)

end LeanLab.BHP1997.DivisorInitialSumFalse561
