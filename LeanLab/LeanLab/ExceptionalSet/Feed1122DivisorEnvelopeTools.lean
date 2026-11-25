import Mathlib
import LeanLab.HeathBrown1985.DivisorEps
import LeanLab.HeathBrown1985.Elementary

/-!
Tools for the two divisor envelopes of P0082, Brudern and Perelli 1998, page 359 displays 14
and 15, burst-20261122 feed1122, session S134.

Elementary inputs, all PROVED here from Mathlib and the lab's PROVED
`HeathBrown1985.card_divisors_le_rpow` and `HeathBrown1985.div_totient_le`:

* `div_totient_le_rpow`: `n/φ(n) ≤ A n^{1/k}`, from `n/φ(n) ≤ e (1 + ω(n)) ≤ e τ(n)`.
* `sum_gcd_mul_le`: the grouping of `q` by `d = (M, q)`, with `(M, r) = 1` and `r ∣ q`
  giving `d r ∣ q`.
* `sum_filter_dvd_inv_le`: `∑_{q ≤ Q, a ∣ q} 1/q ≤ (1 + log Q)/a`.
* `sum_filter_gt_rpow_le`: `∑_{y < j ≤ Q} j^{-7/4} ≤ 3 y^{-3/4}`, by comparison with an integral.
* `truncated_bound` and `tail_bound`: the two envelopes for any `P`, in terms of `τ(M)`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Feed1122DivisorEnvelope

open Real Finset

/-- `1 + ω(n) ≤ τ(n)`. -/
theorem one_add_card_primeFactors_le (n : ℕ) (hn : 1 ≤ n) :
    1 + n.primeFactors.card ≤ n.divisors.card := by
  have h1 : (1 : ℕ) ∉ n.primeFactors := by simp [Nat.mem_primeFactors, Nat.not_prime_one]
  have hsub : insert 1 n.primeFactors ⊆ n.divisors := by
    intro d hd
    rw [Finset.mem_insert] at hd
    rcases hd with rfl | hd
    · exact Nat.mem_divisors.2 ⟨one_dvd _, by omega⟩
    · exact Nat.mem_divisors.2 ⟨Nat.dvd_of_mem_primeFactors hd, by omega⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem h1] at this
  omega

/-- `n/φ(n) ≤ A n^{1/k}` for `n ≥ 1`. -/
theorem div_totient_le_rpow (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) / (n.totient : ℝ) ≤ A * (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  obtain ⟨C, hC, hb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨3 * C, by positivity, fun n hn => ?_⟩
  have h1 := LeanLab.HeathBrown1985.div_totient_le n hn
  have h2 : (1 + (n.primeFactors.card : ℝ)) ≤ n.divisors.card := by
    exact_mod_cast one_add_card_primeFactors_le n hn
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have h3 := hb n hn
  calc (n : ℝ) / n.totient ≤ Real.exp 1 * (1 + n.primeFactors.card) := h1
    _ ≤ 3 * n.divisors.card := mul_le_mul he h2 (by positivity) (by norm_num)
    _ ≤ 3 * (C * (n : ℝ) ^ ((k : ℝ)⁻¹)) := by linarith
    _ = 3 * C * (n : ℝ) ^ ((k : ℝ)⁻¹) := by ring

/-- Grouping by `d = (M, q)`: with `(M, r) = 1` and `r ∣ q`, also `d r ∣ q`. -/
theorem sum_gcd_mul_le (M r : ℕ) (hM : 1 ≤ M) (hcop : Nat.Coprime M r) (S : Finset ℕ)
    (hS : ∀ q ∈ S, r ∣ q) (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q) :
    ∑ q ∈ S, (Nat.gcd M q : ℝ) * w q ≤
      ∑ d ∈ M.divisors, (d : ℝ) * ∑ q ∈ S.filter (fun q => d * r ∣ q), w q := by
  have step : ∀ q ∈ S, (Nat.gcd M q : ℝ) * w q ≤
      ∑ d ∈ M.divisors, (if d * r ∣ q then (d : ℝ) * w q else 0) := by
    intro q hq
    have hg : Nat.gcd M q ∈ M.divisors :=
      Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, by omega⟩
    have hgr : Nat.gcd M q * r ∣ q := by
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop
      · exact Nat.gcd_dvd_right _ _
      · exact hS q hq
    have hnn : ∀ d ∈ M.divisors, (0 : ℝ) ≤ if d * r ∣ q then (d : ℝ) * w q else 0 := by
      intro d _
      split_ifs
      · exact mul_nonneg (by positivity) (hw q)
      · exact le_refl _
    have := Finset.single_le_sum hnn hg
    simpa [hgr] using this
  calc ∑ q ∈ S, (Nat.gcd M q : ℝ) * w q
      ≤ ∑ q ∈ S, ∑ d ∈ M.divisors, (if d * r ∣ q then (d : ℝ) * w q else 0) := sum_le_sum step
    _ = ∑ d ∈ M.divisors, ∑ q ∈ S, (if d * r ∣ q then (d : ℝ) * w q else 0) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d _
      rw [mul_sum, sum_filter]

/-- Reindexing the multiples of `a` in `[1, Q]`. -/
theorem sum_filter_dvd_le (a Q : ℕ) (ha : 1 ≤ a) (p : ℕ → Prop) [DecidablePred p]
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) :
    ∑ q ∈ (Icc 1 Q).filter (fun q => a ∣ q ∧ p q), h q ≤
      ∑ j ∈ (Icc 1 Q).filter (fun j : ℕ => p (a * j)), h (a * j) := by
  have hinj : Set.InjOn (fun j : ℕ => a * j) ((Icc 1 Q).filter (fun j : ℕ => p (a * j)) : Set ℕ) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  rw [← sum_image (f := h) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [mem_filter, mem_Icc] at hq
    obtain ⟨⟨hq1, hqQ⟩, ⟨j, rfl⟩, hp⟩ := hq
    rw [mem_image]
    refine ⟨j, ?_, rfl⟩
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, hp⟩
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · simp [h0] at hq1
      · exact h0
    · exact le_trans (Nat.le_mul_of_pos_left j (by omega)) hqQ
  · intro _ _ _
    exact hh _

/-- `∑_{q ≤ Q, a ∣ q} 1/q ≤ (1 + log Q)/a`. -/
theorem sum_filter_dvd_inv_le (a Q : ℕ) (ha : 1 ≤ a) :
    ∑ q ∈ (Icc 1 Q).filter (fun q => a ∣ q ∧ True), (1 : ℝ) / q ≤ (1 + Real.log Q) / a := by
  have h := sum_filter_dvd_le a Q ha (fun _ => True) (fun q => (1 : ℝ) / q)
    (fun n => by positivity)
  have hsub : ∑ j ∈ (Icc 1 Q).filter (fun _ => True), (1 : ℝ) / ((a * j : ℕ) : ℝ) =
      (1 / (a : ℝ)) * ∑ j ∈ Icc 1 Q, (1 : ℝ) / j := by
    rw [filter_true_of_mem (fun _ _ => trivial), mul_sum]
    apply sum_congr rfl
    intro j _
    rw [Nat.cast_mul, one_div_mul_one_div]
  have hH : ∑ j ∈ Icc 1 Q, (1 : ℝ) / j ≤ 1 + Real.log Q := by
    have := harmonic_le_one_add_log Q
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [one_div] using this
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  calc _ ≤ _ := h
    _ = (1 / (a : ℝ)) * ∑ j ∈ Icc 1 Q, (1 : ℝ) / j := hsub
    _ ≤ (1 / (a : ℝ)) * (1 + Real.log Q) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = (1 + Real.log Q) / a := by ring

/-- Integral comparison: `∑_{i < n} (J + i + 1)^{-7/4} ≤ (4/3) J^{-3/4}` for `J ≥ 1`. -/
theorem sum_range_rpow_le (J n : ℕ) (hJ : 1 ≤ J) :
    ∑ i ∈ range n, ((J : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-(7 : ℝ) / 4) ≤
      4 / 3 * (J : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(7 : ℝ) / 4)) (Set.Icc (J : ℝ) (J + n)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hJ0 hx.1) hxy (by norm_num)
  have h := hanti.sum_le_integral
  beta_reduce at h
  have hint : ∫ x in (J : ℝ)..(J + n), x ^ (-(7 : ℝ) / 4) =
      (((J : ℝ) + n) ^ (-(7 : ℝ) / 4 + 1) - (J : ℝ) ^ (-(7 : ℝ) / 4 + 1)) /
        (-(7 : ℝ) / 4 + 1) := by
    apply integral_rpow
    right
    refine ⟨by norm_num, ?_⟩
    rw [Set.uIcc_of_le (by linarith)]
    intro h0
    exact absurd h0.1 (by linarith)
  rw [hint] at h
  have e1 : (-(7 : ℝ) / 4 + 1) = -(3 : ℝ) / 4 := by norm_num
  rw [e1] at h
  have hpos : (0 : ℝ) ≤ ((J : ℝ) + n) ^ (-(3 : ℝ) / 4) := by positivity
  have e2 : (((J : ℝ) + n) ^ (-(3 : ℝ) / 4) - (J : ℝ) ^ (-(3 : ℝ) / 4)) / (-(3 : ℝ) / 4) =
      4 / 3 * ((J : ℝ) ^ (-(3 : ℝ) / 4) - ((J : ℝ) + n) ^ (-(3 : ℝ) / 4)) := by ring
  rw [e2] at h
  linarith

/-- `∑_{J < j ≤ Q} j^{-7/4} ≤ (4/3) J^{-3/4}` for `J ≥ 1`. -/
theorem sum_filter_gt_nat_le (J Q : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ (Icc 1 Q).filter (fun j : ℕ => J < j), (j : ℝ) ^ (-(7 : ℝ) / 4) ≤
      4 / 3 * (J : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hinj : Set.InjOn (fun i => J + (i + 1)) (range Q : Set ℕ) := by
    intro x _ y _ hxy
    simp only at hxy
    omega
  calc _ ≤ ∑ j ∈ (range Q).image (fun i => J + (i + 1)), (j : ℝ) ^ (-(7 : ℝ) / 4) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj
          rw [mem_image]
          exact ⟨j - J - 1, by simp only [mem_range]; omega, by omega⟩
        · intro j _ _
          positivity
    _ = ∑ i ∈ range Q, ((J + (i + 1) : ℕ) : ℝ) ^ (-(7 : ℝ) / 4) := sum_image hinj
    _ = ∑ i ∈ range Q, ((J : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-(7 : ℝ) / 4) := by
        apply sum_congr rfl
        intro i _
        rw [Nat.cast_add J (i + 1)]
    _ ≤ _ := sum_range_rpow_le J Q hJ

/-- `∑_{y < j ≤ Q} j^{-7/4} ≤ 3 y^{-3/4}` for `y > 0`. -/
theorem sum_filter_gt_rpow_le (y : ℝ) (hy : 0 < y) (Q : ℕ) :
    ∑ j ∈ (Icc 1 Q).filter (fun j : ℕ => y < (j : ℝ)), (j : ℝ) ^ (-(7 : ℝ) / 4) ≤
      3 * y ^ (-(3 : ℝ) / 4) := by
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (j : ℝ) ^ (-(7 : ℝ) / 4) := fun j => by positivity
  rcases lt_or_ge y 1 with hy1 | hy1
  · have hsub : (Icc 1 Q).filter (fun j : ℕ => y < (j : ℝ)) ⊆
        insert 1 ((Icc 1 Q).filter (fun j : ℕ => 1 < j)) := by
      intro j hj
      simp only [mem_filter, mem_Icc] at hj
      rw [mem_insert, mem_filter, mem_Icc]
      by_cases h1 : j = 1
      · left
        exact h1
      · right
        exact ⟨hj.1, by omega⟩
    have hnot : (1 : ℕ) ∉ (Icc 1 Q).filter (fun j : ℕ => 1 < j) := by simp
    have hrest := sum_filter_gt_nat_le 1 Q le_rfl
    have hy3 : 1 ≤ y ^ (-(3 : ℝ) / 4) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1.le (by norm_num)
    simp only [Nat.cast_one, Real.one_rpow] at hrest
    calc _ ≤ ∑ j ∈ insert 1 ((Icc 1 Q).filter (fun j : ℕ => 1 < j)), (j : ℝ) ^ (-(7 : ℝ) / 4) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnn j)
      _ = 1 + ∑ j ∈ (Icc 1 Q).filter (fun j : ℕ => 1 < j), (j : ℝ) ^ (-(7 : ℝ) / 4) := by
          rw [sum_insert hnot]
          simp
      _ ≤ 3 * y ^ (-(3 : ℝ) / 4) := by linarith
  · set J := ⌊y⌋₊ with hJdef
    have hJ1 : 1 ≤ J := Nat.le_floor (by exact_mod_cast hy1)
    have hJy : (J : ℝ) ≤ y := Nat.floor_le hy.le
    have hyJ : y < J + 1 := Nat.lt_floor_add_one y
    have hsub : (Icc 1 Q).filter (fun j : ℕ => y < (j : ℝ)) ⊆ (Icc 1 Q).filter (fun j : ℕ => J < j) := by
      intro j hj
      simp only [mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      exact_mod_cast lt_of_le_of_lt hJy hj.2
    have hmain := sum_filter_gt_nat_le J Q hJ1
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    have hy2 : y / 2 ≤ J := by linarith
    have hpow : (J : ℝ) ^ (-(3 : ℝ) / 4) ≤ (y / 2) ^ (-(3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hy2 (by norm_num)
    have hsplit : (y / 2) ^ (-(3 : ℝ) / 4) =
        y ^ (-(3 : ℝ) / 4) * (1 / 2 : ℝ) ^ (-(3 : ℝ) / 4) := by
      rw [div_eq_mul_one_div, Real.mul_rpow hy.le (by norm_num)]
    have hhalf : (1 / 2 : ℝ) ^ (-(3 : ℝ) / 4) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_ge (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
        (show (-1 : ℝ) ≤ -(3 : ℝ) / 4 by norm_num)
      have e : (1 / 2 : ℝ) ^ (-1 : ℝ) = 2 := by rw [Real.rpow_neg_one]; norm_num
      linarith
    have hypos : 0 ≤ y ^ (-(3 : ℝ) / 4) := by positivity
    rw [hsplit] at hpow
    calc _ ≤ ∑ j ∈ (Icc 1 Q).filter (fun j : ℕ => J < j), (j : ℝ) ^ (-(7 : ℝ) / 4) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnn j)
      _ ≤ 4 / 3 * (J : ℝ) ^ (-(3 : ℝ) / 4) := hmain
      _ ≤ 4 / 3 * (y ^ (-(3 : ℝ) / 4) * 2) := by nlinarith
      _ ≤ 3 * y ^ (-(3 : ℝ) / 4) := by nlinarith

/-- Display 14 for any `P ≥ 1`: given `n/φ(n) ≤ A n^{1/8}`, the truncated envelope is at most
`A² P^{1/4} τ(M) (1 + log P)/P`. -/
theorem truncated_bound (A P : ℝ) (hA : 0 ≤ A) (hP : 1 ≤ P) (r M : ℕ) (hr : 1 ≤ r)
    (hM : 1 ≤ M) (hcop : Nat.Coprime M r)
    (hB : ∀ n : ℕ, 1 ≤ n → (n : ℝ) / n.totient ≤ A * (n : ℝ) ^ ((1 : ℝ) / 8)) :
    (r : ℝ) / P * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
        (q : ℝ) / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ))
      ≤ A ^ 2 * P ^ ((1 : ℝ) / 4) * (M.divisors.card : ℝ) * (1 + Real.log P) / P := by
  set Q := ⌊P⌋₊ with hQ
  set S := (Icc 1 Q).filter (fun q => r ∣ q) with hS
  have hP0 : (0 : ℝ) < P := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hP8 : 0 ≤ A * P ^ ((1 : ℝ) / 8) := by positivity
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hP)
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hQP : (Q : ℝ) ≤ P := Nat.floor_le hP0.le
  have key : ∀ q ∈ S, (q : ℝ) / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ)) ≤
      A ^ 2 * P ^ ((1 : ℝ) / 4) * ((Nat.gcd M q : ℝ) * (1 / (q : ℝ))) := by
    intro q hq
    simp only [hS, mem_filter, mem_Icc] at hq
    obtain ⟨⟨hq1, hqQ⟩, _⟩ := hq
    have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hqQ) hQP
    have hg1 : 1 ≤ Nat.gcd M q := Nat.gcd_pos_of_pos_left _ (by omega)
    have hlg : q / Nat.gcd M q * Nat.gcd M q = q := Nat.div_mul_cancel (Nat.gcd_dvd_right M q)
    set g := Nat.gcd M q
    set l := q / g
    have hl1 : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · rw [h0] at hlg
        omega
      · exact h0
    have hlq : l ≤ q := Nat.div_le_self q g
    have hφq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hφl : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
    have hg0 : (0 : ℝ) < g := by exact_mod_cast hg1
    have hlgR : (l : ℝ) * g = q := by exact_mod_cast hlg
    have e : (q : ℝ) / ((q.totient : ℝ) * (l.totient : ℝ)) =
        ((q : ℝ) / q.totient) * ((l : ℝ) / l.totient) * ((g : ℝ) * (1 / (q : ℝ))) := by
      rw [← hlgR]
      field_simp
    have b1 : (q : ℝ) / q.totient ≤ A * P ^ ((1 : ℝ) / 8) :=
      le_trans (hB q hq1)
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq0.le hqP (by norm_num)) hA)
    have b2 : (l : ℝ) / l.totient ≤ A * P ^ ((1 : ℝ) / 8) :=
      le_trans (hB l hl1) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hl0.le
        (le_trans (by exact_mod_cast hlq) hqP) (by norm_num)) hA)
    have hP14 : P ^ ((1 : ℝ) / 4) = P ^ ((1 : ℝ) / 8) * P ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_add hP0]
      norm_num
    rw [e, hP14]
    have hw : 0 ≤ (g : ℝ) * (1 / (q : ℝ)) := by positivity
    calc ((q : ℝ) / q.totient) * ((l : ℝ) / l.totient) * ((g : ℝ) * (1 / (q : ℝ)))
        ≤ (A * P ^ ((1 : ℝ) / 8)) * (A * P ^ ((1 : ℝ) / 8)) * ((g : ℝ) * (1 / (q : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ hw
          exact mul_le_mul b1 b2 (by positivity) hP8
      _ = _ := by ring
  have hsum1 : ∑ q ∈ S, (q : ℝ) / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ)) ≤
      A ^ 2 * P ^ ((1 : ℝ) / 4) * ∑ q ∈ S, (Nat.gcd M q : ℝ) * (1 / (q : ℝ)) := by
    rw [mul_sum]
    exact sum_le_sum key
  have hsum2 := sum_gcd_mul_le M r hM hcop S (fun q hq => (mem_filter.1 hq).2)
    (fun q => 1 / (q : ℝ)) (fun q => by positivity)
  have hlogQ : 0 ≤ 1 + Real.log Q := by linarith [Real.log_nonneg hQR]
  have hinner : ∀ d ∈ M.divisors,
      (d : ℝ) * ∑ q ∈ S.filter (fun q => d * r ∣ q), 1 / (q : ℝ) ≤ (1 + Real.log Q) / r := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdr : 1 ≤ d * r := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hsub : S.filter (fun q => d * r ∣ q) ⊆ (Icc 1 Q).filter (fun q => d * r ∣ q ∧ True) := by
      intro q hq
      simp only [hS, mem_filter] at hq ⊢
      exact ⟨hq.1.1, hq.2, trivial⟩
    have h1 : ∑ q ∈ S.filter (fun q => d * r ∣ q), 1 / (q : ℝ) ≤
        ∑ q ∈ (Icc 1 Q).filter (fun q => d * r ∣ q ∧ True), 1 / (q : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    have h2 := sum_filter_dvd_inv_le (d * r) Q hdr
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    calc (d : ℝ) * _ ≤ (d : ℝ) * ((1 + Real.log Q) / ((d * r : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hd0.le
      _ = (1 + Real.log Q) / r := by
          push_cast
          field_simp
  have hsum3 : ∑ q ∈ S, (Nat.gcd M q : ℝ) * (1 / (q : ℝ)) ≤
      (M.divisors.card : ℝ) * ((1 + Real.log Q) / r) := by
    refine hsum2.trans ?_
    calc _ ≤ ∑ d ∈ M.divisors, (1 + Real.log Q) / r := sum_le_sum hinner
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hlog : Real.log Q ≤ Real.log P := Real.log_le_log (by linarith) hQP
  have hA4 : 0 ≤ A ^ 2 * P ^ ((1 : ℝ) / 4) := by positivity
  calc (r : ℝ) / P * ∑ q ∈ S, (q : ℝ) / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ))
      ≤ (r : ℝ) / P * (A ^ 2 * P ^ ((1 : ℝ) / 4) *
          ((M.divisors.card : ℝ) * ((1 + Real.log Q) / r))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum1.trans (mul_le_mul_of_nonneg_left hsum3 hA4)
    _ = A ^ 2 * P ^ ((1 : ℝ) / 4) * (M.divisors.card : ℝ) * (1 + Real.log Q) / P := by
        field_simp
    _ ≤ _ := by gcongr

/-- Display 15 for any `P > 0`: given `n/φ(n) ≤ A n^{1/8}`, the tail envelope is at most
`3 A² τ(M) P^{-3/4}`. -/
theorem tail_bound (A P : ℝ) (hA : 0 ≤ A) (hP : 0 < P) (r M : ℕ) (hr : 1 ≤ r) (hM : 1 ≤ M)
    (hcop : Nat.Coprime M r)
    (hB : ∀ n : ℕ, 1 ≤ n → (n : ℝ) / n.totient ≤ A * (n : ℝ) ^ ((1 : ℝ) / 8)) :
    (r : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) ∧ r ∣ q then
        1 / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ)) else 0)
      ≤ 3 * A ^ 2 * (M.divisors.card : ℝ) * P ^ (-(3 : ℝ) / 4) := by
  set K := 3 * A ^ 2 * (M.divisors.card : ℝ) * P ^ (-(3 : ℝ) / 4) with hKdef
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hK : 0 ≤ K := by positivity
  have hfin : ∀ Q : ℕ, ∑ q ∈ (Icc 1 Q).filter (fun q : ℕ => r ∣ q ∧ P < (q : ℝ)),
      1 / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ)) ≤ K / r := by
    intro Q
    set T := (Icc 1 Q).filter (fun q : ℕ => r ∣ q ∧ P < (q : ℝ)) with hT
    have key : ∀ q ∈ T, 1 / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ)) ≤
        A ^ 2 * ((Nat.gcd M q : ℝ) * (q : ℝ) ^ (-(7 : ℝ) / 4)) := by
      intro q hq
      simp only [hT, mem_filter, mem_Icc] at hq
      obtain ⟨⟨hq1, _⟩, _, _⟩ := hq
      have hg1 : 1 ≤ Nat.gcd M q := Nat.gcd_pos_of_pos_left _ (by omega)
      have hlg : q / Nat.gcd M q * Nat.gcd M q = q :=
        Nat.div_mul_cancel (Nat.gcd_dvd_right M q)
      set g := Nat.gcd M q
      set l := q / g
      have hl1 : 1 ≤ l := by
        rcases Nat.eq_zero_or_pos l with h0 | h0
        · rw [h0] at hlg
          omega
        · exact h0
      have hlq : l ≤ q := Nat.div_le_self q g
      have hφq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hφl : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
      have hg0 : (0 : ℝ) < g := by exact_mod_cast hg1
      have hlgR : (l : ℝ) * g = q := by exact_mod_cast hlg
      have e : 1 / ((q.totient : ℝ) * (l.totient : ℝ)) =
          ((q : ℝ) / q.totient) * ((l : ℝ) / l.totient) * ((g : ℝ) * (1 / (q : ℝ) ^ 2)) := by
        rw [← hlgR]
        field_simp
      have b1 : (q : ℝ) / q.totient ≤ A * (q : ℝ) ^ ((1 : ℝ) / 8) := hB q hq1
      have b2 : (l : ℝ) / l.totient ≤ A * (q : ℝ) ^ ((1 : ℝ) / 8) :=
        le_trans (hB l hl1) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hl0.le
          (by exact_mod_cast hlq) (by norm_num)) hA)
      have hpow : (q : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) ^ ((1 : ℝ) / 8) * (1 / (q : ℝ) ^ 2) =
          (q : ℝ) ^ (-(7 : ℝ) / 4) := by
        have h2 : (1 : ℝ) / (q : ℝ) ^ 2 = (q : ℝ) ^ (-(2 : ℝ)) := by
          rw [Real.rpow_neg hq0.le, Real.rpow_two, one_div]
        rw [h2, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        norm_num
      rw [e]
      have hw : 0 ≤ (g : ℝ) * (1 / (q : ℝ) ^ 2) := by positivity
      calc ((q : ℝ) / q.totient) * ((l : ℝ) / l.totient) * ((g : ℝ) * (1 / (q : ℝ) ^ 2))
          ≤ (A * (q : ℝ) ^ ((1 : ℝ) / 8)) * (A * (q : ℝ) ^ ((1 : ℝ) / 8)) *
              ((g : ℝ) * (1 / (q : ℝ) ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ hw
            exact mul_le_mul b1 b2 (by positivity) (by positivity)
        _ = A ^ 2 * ((g : ℝ) * ((q : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) ^ ((1 : ℝ) / 8) *
              (1 / (q : ℝ) ^ 2))) := by ring
        _ = _ := by rw [hpow]
    have hsum1 : ∑ q ∈ T, 1 / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ)) ≤
        A ^ 2 * ∑ q ∈ T, (Nat.gcd M q : ℝ) * (q : ℝ) ^ (-(7 : ℝ) / 4) := by
      rw [mul_sum]
      exact sum_le_sum key
    have hsum2 := sum_gcd_mul_le M r hM hcop T (fun q hq => (mem_filter.1 hq).2.1)
      (fun q => (q : ℝ) ^ (-(7 : ℝ) / 4)) (fun q => by positivity)
    have hinner : ∀ d ∈ M.divisors,
        (d : ℝ) * ∑ q ∈ T.filter (fun q => d * r ∣ q), (q : ℝ) ^ (-(7 : ℝ) / 4) ≤
          3 * P ^ (-(3 : ℝ) / 4) / r := by
      intro d hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
      set a := d * r with ha
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (by positivity)
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hsub : T.filter (fun q => a ∣ q) ⊆
          (Icc 1 Q).filter (fun q : ℕ => a ∣ q ∧ P < (q : ℝ)) := by
        intro q hq
        simp only [hT, mem_filter] at hq ⊢
        exact ⟨hq.1.1, hq.2, hq.1.2.2⟩
      have h1 : ∑ q ∈ T.filter (fun q => a ∣ q), (q : ℝ) ^ (-(7 : ℝ) / 4) ≤
          ∑ q ∈ (Icc 1 Q).filter (fun q : ℕ => a ∣ q ∧ P < (q : ℝ)), (q : ℝ) ^ (-(7 : ℝ) / 4) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
      have h2 := sum_filter_dvd_le a Q ha1 (fun q : ℕ => P < (q : ℝ))
        (fun q => (q : ℝ) ^ (-(7 : ℝ) / 4)) (fun q => by positivity)
      have h3 : ∑ j ∈ (Icc 1 Q).filter (fun j : ℕ => P < ((a * j : ℕ) : ℝ)),
          ((a * j : ℕ) : ℝ) ^ (-(7 : ℝ) / 4) =
          (a : ℝ) ^ (-(7 : ℝ) / 4) *
            ∑ j ∈ (Icc 1 Q).filter (fun j : ℕ => P / a < (j : ℝ)), (j : ℝ) ^ (-(7 : ℝ) / 4) := by
        rw [mul_sum]
        apply sum_congr
        · apply filter_congr
          intro j _
          rw [Nat.cast_mul, div_lt_iff₀ ha0, mul_comm]
        · intro j _
          rw [Nat.cast_mul, Real.mul_rpow ha0.le (Nat.cast_nonneg j)]
      have h4 := sum_filter_gt_rpow_le (P / a) (by positivity) Q
      have h5 : (a : ℝ) ^ (-(7 : ℝ) / 4) * (3 * (P / a) ^ (-(3 : ℝ) / 4)) =
          3 * P ^ (-(3 : ℝ) / 4) / a := by
        rw [Real.div_rpow hP.le ha0.le]
        have : (a : ℝ) ^ (-(7 : ℝ) / 4) = (a : ℝ) ^ (-(3 : ℝ) / 4) * (a : ℝ) ^ (-1 : ℝ) := by
          rw [← Real.rpow_add ha0]
          norm_num
        rw [this, Real.rpow_neg_one]
        have : (0 : ℝ) < (a : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
        field_simp
      have hapos : (0 : ℝ) ≤ (a : ℝ) ^ (-(7 : ℝ) / 4) := by positivity
      have hchain : ∑ q ∈ T.filter (fun q => a ∣ q), (q : ℝ) ^ (-(7 : ℝ) / 4) ≤
          3 * P ^ (-(3 : ℝ) / 4) / a := by
        calc _ ≤ _ := h1
          _ ≤ _ := h2
          _ = _ := h3
          _ ≤ (a : ℝ) ^ (-(7 : ℝ) / 4) * (3 * (P / a) ^ (-(3 : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_left h4 hapos
          _ = _ := h5
      calc (d : ℝ) * _ ≤ (d : ℝ) * (3 * P ^ (-(3 : ℝ) / 4) / a) :=
            mul_le_mul_of_nonneg_left hchain hd0.le
        _ = 3 * P ^ (-(3 : ℝ) / 4) / r := by
            rw [ha]
            push_cast
            field_simp
    have hsum3 : ∑ q ∈ T, (Nat.gcd M q : ℝ) * (q : ℝ) ^ (-(7 : ℝ) / 4) ≤
        (M.divisors.card : ℝ) * (3 * P ^ (-(3 : ℝ) / 4) / r) := by
      refine hsum2.trans ?_
      calc _ ≤ ∑ d ∈ M.divisors, 3 * P ^ (-(3 : ℝ) / 4) / r := sum_le_sum hinner
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    calc _ ≤ _ := hsum1
      _ ≤ A ^ 2 * ((M.divisors.card : ℝ) * (3 * P ^ (-(3 : ℝ) / 4) / r)) :=
          mul_le_mul_of_nonneg_left hsum3 (by positivity)
      _ = K / r := by
          rw [hKdef]
          ring
  have htsum : ∑' q : ℕ, (if P < (q : ℝ) ∧ r ∣ q then
        1 / ((q.totient : ℝ) * ((q / Nat.gcd M q).totient : ℝ)) else 0) ≤ K / r := by
    refine tsum_le_of_sum_le' (by positivity) (fun s => ?_)
    rw [← sum_filter]
    refine le_trans ?_ (hfin (s.sup id))
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [mem_filter, mem_Icc] at hq ⊢
      obtain ⟨hqs, hPq, hrq⟩ := hq
      have hq0 : (0 : ℝ) < q := lt_trans hP hPq
      refine ⟨⟨?_, Finset.le_sup (f := id) hqs⟩, hrq, hPq⟩
      exact_mod_cast hq0
    · intro q _ _
      positivity
  calc (r : ℝ) * _ ≤ (r : ℝ) * (K / r) := mul_le_mul_of_nonneg_left htsum hr0.le
    _ = K := by field_simp

end LeanLab.ExceptionalSet.Feed1122DivisorEnvelope
