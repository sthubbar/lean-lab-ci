/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, citing Vaughan, The Hardy-Littlewood
Method, Cambridge 1981, book page 34, the elementary fact under display 3.23:
Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, together with the convergence of Σ_q φ(q)^{-2}.
Proof used here, elementary and fully finite: (n/φ(n))² = Π_{p|n} (p/(p-1))² ≤ Π_{p|n} (1+6/p)
= Σ_{t ⊆ primes of n} Π_{p∈t} 6/p; swap the sums, bound the tail Σ_{m>W} m^{-2} ≤ 2 min(1/W,1)
by Mathlib's `sum_Ioo_inv_sq_le`, and bound Σ_{t} Π_{p∈t} 6/p² = Π_p (1+6/p²) ≤ exp 6.
Burst burst-20261122 session S72. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a

namespace LeanLab.BHP1997.TotientTailS72

open Finset

/-- Tail of Σ m^{-2}: for W > 0, Σ_{1 ≤ m ≤ R, W < m} 1/m² ≤ 2 min(1/W, 1). -/
theorem inv_sq_tail_le (W : ℝ) (hW : 0 < W) (R : ℕ) :
    ∑ m ∈ (Icc 1 R).filter (fun m : ℕ => W < (m : ℝ)), 1 / (m : ℝ) ^ 2 ≤
      2 * min (1 / W) 1 := by
  set k := ⌊W⌋₊ with hk
  have hsub : (Icc 1 R).filter (fun m : ℕ => W < (m : ℝ)) ⊆ Ioo k (R + 1) := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    simp only [mem_Ioo]
    exact ⟨(Nat.floor_lt hW.le).2 hm.2, by omega⟩
  have h1 : ∑ m ∈ (Icc 1 R).filter (fun m : ℕ => W < (m : ℝ)), 1 / (m : ℝ) ^ 2 ≤
      ∑ m ∈ Ioo k (R + 1), ((m : ℝ) ^ 2)⁻¹ := by
    simp only [one_div]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h2 := sum_Ioo_inv_sq_le (α := ℝ) k (R + 1)
  have hk1 : W < (k : ℝ) + 1 := Nat.lt_floor_add_one W
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h3 : 2 / ((k : ℝ) + 1) ≤ 2 * min (1 / W) 1 := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine le_min ?_ ?_
    · rw [mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) hW hk1.le
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- Multiples of d in the tail: Σ_{1 ≤ n ≤ R, Z < n, d ∣ n} 1/n² ≤ (2/d) min(1/Z, 1). -/
theorem inv_sq_tail_dvd_le (Z : ℝ) (hZ : 0 < Z) (R d : ℕ) (hd : 1 ≤ d) :
    ∑ n ∈ (Icc 1 R).filter (fun n : ℕ => Z < (n : ℝ)),
        (if d ∣ n then 1 / (n : ℝ) ^ 2 else 0) ≤ 2 / d * min (1 / Z) 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set B := (Icc 1 R).filter (fun m : ℕ => Z / d < (m : ℝ)) with hB
  rw [← sum_filter]
  have hsub : ((Icc 1 R).filter (fun n : ℕ => Z < (n : ℝ))).filter (fun n => d ∣ n) ⊆
      B.image (fun m => d * m) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnR⟩, hZn⟩, m, rfl⟩ := hn
    refine mem_image.2 ⟨m, ?_, rfl⟩
    simp only [hB, mem_filter, mem_Icc]
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hn1
      · exact h
    refine ⟨⟨hm1, le_trans (Nat.le_mul_of_pos_left m (by omega)) hnR⟩, ?_⟩
    rw [div_lt_iff₀ hd0]
    push_cast at hZn
    linarith
  have hinj : Set.InjOn (fun m => d * m) (B : Set ℕ) := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  calc ∑ n ∈ ((Icc 1 R).filter (fun n : ℕ => Z < (n : ℝ))).filter (fun n => d ∣ n),
          1 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ B.image (fun m => d * m), 1 / (n : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ m ∈ B, 1 / ((d * m : ℕ) : ℝ) ^ 2 := sum_image hinj
    _ = 1 / (d : ℝ) ^ 2 * ∑ m ∈ B, 1 / (m : ℝ) ^ 2 := by
        rw [mul_sum]; refine sum_congr rfl fun m _ => ?_
        push_cast; rw [mul_pow, one_div_mul_one_div]
    _ ≤ 1 / (d : ℝ) ^ 2 * (2 * min (1 / (Z / d)) 1) := by
        gcongr
        exact inv_sq_tail_le (Z / d) (div_pos hZ hd0) R
    _ ≤ 2 / d * min (1 / Z) 1 := by
        have hmin : min (1 / (Z / d)) 1 ≤ (d : ℝ) * min (1 / Z) 1 := by
          rw [mul_min_of_nonneg _ _ hd0.le, one_div_div, mul_one_div, mul_one]
          exact min_le_min_left _ (by exact_mod_cast hd)
        calc 1 / (d : ℝ) ^ 2 * (2 * min (1 / (Z / d)) 1)
            ≤ 1 / (d : ℝ) ^ 2 * (2 * ((d : ℝ) * min (1 / Z) 1)) := by gcongr
          _ = 2 / d * min (1 / Z) 1 := by field_simp

/-- Pointwise: for n ≥ 1, (n/φ(n))² ≤ Σ_{t ⊆ primeFactors n} Π_{p∈t} 6/p. -/
theorem sq_div_totient_le (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) / (Nat.totient n : ℝ)) ^ 2 ≤
      ∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t, (6 / (p : ℝ)) := by
  have hphi : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have key := Nat.totient_mul_prod_primeFactors n
  have hkeyR : (Nat.totient n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) key
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    refine prod_congr rfl fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub this, Nat.cast_one]
  have hpos : ∀ p ∈ n.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast this
    linarith
  have hP1 : (0 : ℝ) < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := prod_pos hpos
  have hratio : (n : ℝ) / (Nat.totient n : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [prod_div_distrib, div_eq_div_iff hphi.ne' hP1.ne']
    linarith [hkeyR]
  rw [hratio, ← prod_pow, ← prod_one_add]
  refine prod_le_prod₀ (fun p hp => by positivity) (fun p hp => ?_)
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_pow, div_le_iff₀ (by positivity)]
  have : (1 + 6 / (p : ℝ)) * ((p : ℝ) - 1) ^ 2 = ((p : ℝ) ^ 3 + 4 * p ^ 2 - 11 * p + 6) / p := by
    field_simp; ring
  rw [this, le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * p - 3) (by linarith : (0 : ℝ) ≤ p - 2)]

/-- Euler product bound: Σ_{t ⊆ P} Π_{p∈t} 6/p² ≤ exp 6 for any finite set P of primes. -/
theorem sum_powerset_prod_le (R : ℕ) :
    ∑ t ∈ ((Icc 1 R).filter Nat.Prime).powerset, ∏ p ∈ t, (6 / (p : ℝ) ^ 2) ≤ Real.exp 6 := by
  set P := (Icc 1 R).filter Nat.Prime
  rw [← prod_one_add]
  calc ∏ p ∈ P, (1 + 6 / (p : ℝ) ^ 2) ≤ ∏ p ∈ P, Real.exp (6 / (p : ℝ) ^ 2) := by
        refine prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
        have := Real.add_one_le_exp (6 / (p : ℝ) ^ 2)
        linarith
    _ = Real.exp (∑ p ∈ P, 6 / (p : ℝ) ^ 2) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 6 := by
        rw [Real.exp_le_exp]
        have hsub : P ⊆ Ioo 1 (R + 1) := by
          intro p hp
          simp only [P, mem_filter, mem_Icc] at hp
          simp only [mem_Ioo]
          exact ⟨hp.2.one_lt, by omega⟩
        have h2 := sum_Ioo_inv_sq_le (α := ℝ) 1 (R + 1)
        calc ∑ p ∈ P, 6 / (p : ℝ) ^ 2 = 6 * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by
              rw [mul_sum]; exact sum_congr rfl fun _ _ => by rw [div_eq_mul_inv]
          _ ≤ 6 * ∑ p ∈ Ioo 1 (R + 1), ((p : ℝ) ^ 2)⁻¹ := by
              gcongr
          _ ≤ 6 := by norm_num at h2; linarith

/-- Vaughan 1981 page 34, under display 3.23: Σ_{Z < r ≤ R} φ(r)^{-2} ≤ K min(1/Z, 1),
uniformly in R, with K = 2 e^6. Identical statement to
`Section2MS.leaf_totient_sq_tail512`. -/
theorem totient_sq_tail (Z : ℝ) (hZ : 0 < Z) (R : ℕ) :
    ∑ r ∈ (Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2 ≤ 2 * Real.exp 6 * min (1 / Z) 1 := by
  set A := (Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)) with hA
  set P := (Icc 1 R).filter Nat.Prime with hP
  set M := min (1 / Z) 1 with hM
  have hM0 : 0 ≤ M := le_min (by positivity) zero_le_one
  let w : Finset ℕ → ℝ := fun t => ∏ p ∈ t, (6 / (p : ℝ))
  have hw0 : ∀ t, 0 ≤ w t := fun t => prod_nonneg fun p _ => by positivity
  -- step 1: pointwise bound, rewritten as a sum over subsets of P
  have step1 : ∀ n ∈ A, 1 / (Nat.totient n : ℝ) ^ 2 ≤
      ∑ t ∈ P.powerset, (if t ⊆ n.primeFactors then w t * (1 / (n : ℝ) ^ 2) else 0) := by
    intro n hn
    simp only [hA, mem_filter, mem_Icc] at hn
    have hn1 := hn.1.1
    have hphi : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hb := sq_div_totient_le n hn1
    have hfilt : P.powerset.filter (fun t => t ⊆ n.primeFactors) = n.primeFactors.powerset := by
      ext t
      simp only [mem_filter, mem_powerset]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun p hp => ?_, h⟩
        have hp' := h hp
        simp only [hP, mem_filter, mem_Icc]
        refine ⟨⟨(Nat.prime_of_mem_primeFactors hp').one_le, ?_⟩,
          Nat.prime_of_mem_primeFactors hp'⟩
        exact le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp')) hn.1.2
    rw [← sum_filter, hfilt, ← sum_mul]
    rw [div_pow] at hb
    rw [div_le_iff₀ (by positivity)] at hb
    rw [one_div, inv_eq_one_div, div_le_iff₀ (by positivity)]
    calc (1 : ℝ) ≤ (∑ t ∈ n.primeFactors.powerset, w t) * (Nat.totient n : ℝ) ^ 2 /
          (n : ℝ) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]; simpa [w] using hb
      _ = (∑ t ∈ n.primeFactors.powerset, w t) * (1 / (n : ℝ) ^ 2) *
          (Nat.totient n : ℝ) ^ 2 := by ring
  -- step 2: swap the sums
  have step2 : ∑ n ∈ A, 1 / (Nat.totient n : ℝ) ^ 2 ≤
      ∑ t ∈ P.powerset, w t * ∑ n ∈ A,
        (if (∏ p ∈ t, p) ∣ n then 1 / (n : ℝ) ^ 2 else 0) := by
    refine (sum_le_sum step1).trans ?_
    rw [sum_comm]
    refine sum_le_sum fun t _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    by_cases ht : t ⊆ n.primeFactors
    · have hd : (∏ p ∈ t, p) ∣ n :=
        (prod_dvd_prod_of_subset t n.primeFactors (fun p => p) ht).trans
          (Nat.prod_primeFactors_dvd n)
      simp [ht, hd]
    · simp only [ht, ite_false]
      exact mul_nonneg (hw0 t) (by split_ifs <;> positivity)
  -- step 3: the inner tail bound and the Euler product
  have hdpos : ∀ t ∈ P.powerset, 1 ≤ ∏ p ∈ t, p := by
    intro t ht
    rw [mem_powerset] at ht
    refine Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => ?_)
    have := ht hp
    simp only [hP, mem_filter] at this
    exact this.2.ne_zero
  calc ∑ n ∈ A, 1 / (Nat.totient n : ℝ) ^ 2
      ≤ ∑ t ∈ P.powerset, w t * ∑ n ∈ A,
        (if (∏ p ∈ t, p) ∣ n then 1 / (n : ℝ) ^ 2 else 0) := step2
    _ ≤ ∑ t ∈ P.powerset, w t * (2 / ((∏ p ∈ t, p : ℕ) : ℝ) * M) := by
        refine sum_le_sum fun t ht => ?_
        exact mul_le_mul_of_nonneg_left
          (inv_sq_tail_dvd_le Z hZ R _ (hdpos t ht)) (hw0 t)
    _ = 2 * M * ∑ t ∈ P.powerset, ∏ p ∈ t, (6 / (p : ℝ) ^ 2) := by
        rw [mul_sum]
        refine sum_congr rfl fun t _ => ?_
        simp only [w]
        rw [Nat.cast_prod, show ∏ p ∈ t, 6 / (p : ℝ) ^ 2 =
            (∏ p ∈ t, 6 / (p : ℝ)) / ∏ p ∈ t, (p : ℝ) by
          rw [← prod_div_distrib]; exact prod_congr rfl fun p _ => by rw [div_div, sq]]
        ring
    _ ≤ 2 * M * Real.exp 6 := by
        gcongr
        exact sum_powerset_prod_le R
    _ = 2 * Real.exp 6 * min (1 / Z) 1 := by rw [hM]; ring

/-- The packaged form, identical statement to `Section2MS.leaf_totient_sq_tail512`. -/
theorem leaf_totient_sq_tail512 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 0 < Z → ∀ R : ℕ,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
          1 / (Nat.totient r : ℝ) ^ 2 ≤ K * min (1 / Z) 1 :=
  ⟨2 * Real.exp 6, by positivity, fun Z hZ R => totient_sq_tail Z hZ R⟩

end LeanLab.BHP1997.TotientTailS72

#print axioms LeanLab.BHP1997.TotientTailS72.inv_sq_tail_le
#print axioms LeanLab.BHP1997.TotientTailS72.inv_sq_tail_dvd_le
#print axioms LeanLab.BHP1997.TotientTailS72.sq_div_totient_le
#print axioms LeanLab.BHP1997.TotientTailS72.sum_powerset_prod_le
#print axioms LeanLab.BHP1997.TotientTailS72.totient_sq_tail
#print axioms LeanLab.BHP1997.TotientTailS72.leaf_totient_sq_tail512
