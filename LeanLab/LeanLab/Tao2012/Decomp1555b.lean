/-
Tao 2012, arXiv 1201.6656v4, Math. Comp. 83 (2014). Unit U-1555, run 20261026T1219Z-15327.

Proposition 4.10, the mesoscopic L² estimate, Section 4: the arithmetic of the off-diagonal sum.
After Siebert's bound the proof needs, for each fixed h',
  ∑_{h ≠ h', 2 | h - h'} ∏_{p | h-h', p>2} (p-1)/(p-2) ≤ H/𝔖₂ + ∑_{n ≤ H} f(n)
by the divisor identity, (4.17) and the Euler product, and then
  𝔖₂ ∑_{n ≤ H} f(n) ≤ (e^γ log log 2H + 2.507/log log 2H) · log(9H)/2
by Rosser and Schoenfeld 1962 Theorem 15 and Ramaré's bound for ∑ μ²(n)/φ(n).

Corrected form: the fetched text prints the Euler product as (1/2) ∏ (1 + f(p)); the identity
that gives 1/𝔖₂ is (1/2) ∏_{p>2} (1 + f(p)/p). The leaf `f_euler_partial` uses the
consequence ∑_{n ≤ N} f(n)/(2n) ≤ 1/𝔖₂, which holds for the corrected product.

Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean
kernel.
-/
import LeanLab.Tao2012.Decomp1555a
import LeanLab.ChenExplicit.GammaBounds

namespace LeanLab.Tao2012.Decomp1555

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

/-- The off-diagonal singular sum for fixed `h'`:
`∑_{1 ≤ h ≤ H, h ≠ h', 2 | h - h'} ∏_{p | h - h', p > 2} (p-1)/(p-2)`. -/
noncomputable def G (H h' : ℕ) : ℝ :=
  ∑ h ∈ (Icc 1 H).erase h',
    (if Even ((h : ℤ) - h') then prodFac ((h : ℤ) - h').natAbs else 0)

/-- `μ²(n)/φ(n)` as a real number. -/
noncomputable def muPhi (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ)

/-! ## Cited inputs -/

/-- Cited, not proved in the lab: Rosser and Schoenfeld 1962, Approximate formulas for some
functions of prime numbers, Theorem 15: for `n ≥ 3`,
`n/φ(n) < e^γ log log n + 2.50637 / log log n`, except for `n = 223092870`, where `2.50637`
becomes `2.51`. Tao uses it with the constant `2.507`, item [43] of his bibliography. -/
theorem rosser_schoenfeld_15 {n : ℕ} (hn : 3 ≤ n) (hne : n ≠ 223092870) :
    (n : ℝ) / Nat.totient n <
      exp eulerMascheroniConstant * log (log n) + 2.50637 / log (log n) := by
  sorry

/-- Cited, not proved in the lab: Ramaré, item [35] of Tao's bibliography, Lemma 3.5, as Tao
uses it in the proof of Proposition 4.10: `∑_{n ≤ N} μ²(n)/φ(n) ≤ log N + 1.4709` for
`N ≥ 1`. -/
theorem ramare_mu_phi {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, muPhi n ≤ log N + 1.4709 := by
  sorry

/-- `f(n) ≥ 0`: every prime factor of an odd `n` is at least `3`. Proved. -/
theorem f_nonneg (n : ℕ) : 0 ≤ f n := by
  unfold f
  split_ifs with h
  · apply prod_nonneg
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr h.1) (even_iff_two_dvd.mpr hdvd)
    have h3 : 3 ≤ p := by have := hpp.two_le; omega
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3
    have : 0 < (p : ℝ) - 2 := by linarith
    positivity
  · exact le_refl 0

/-! ## Leaves -/

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, Section 4: the divisor identity
`∏_{p | k, p > 2} (p-1)/(p-2) = ∑_{n | k} f(n)` for `k ≠ 0`, where
`f(n) = 1_{(n,2)=1} μ²(n) ∏_{p | n, p > 2} 1/(p-2)`. -/
theorem prodFac_eq_divsum {k : ℕ} (hk : k ≠ 0) : prodFac k = ∑ n ∈ k.divisors, f n := by
  classical
  let w : ℕ → ℝ := fun p => if 2 < p then 1 / ((p : ℝ) - 2) else 0
  have hfprod (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
      f (∏ p ∈ t, p) = ∏ p ∈ t, w p := by
    by_cases h2 : 2 ∈ t
    · have hd : 2 ∣ ∏ p ∈ t, p := dvd_prod_of_mem _ h2
      have hodd : ¬ Odd (∏ p ∈ t, p) := fun ho => ho.not_two_dvd_nat hd
      have hf0 : f (∏ p ∈ t, p) = 0 := by simp [f, hodd]
      rw [hf0]
      symm
      apply prod_eq_zero h2
      simp [w]
    · have hodd : Odd (∏ p ∈ t, p) := by
        apply Nat.coprime_two_right.mp
        apply Nat.Coprime.prod_left
        intro p hp
        exact Nat.coprime_two_right.mpr ((ht p hp).odd_of_ne_two (by intro he; exact h2 (he ▸ hp)))
      have hsf : Squarefree (∏ p ∈ t, p) := by
        refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
          (fun p hp => (ht p hp).squarefree)
        change IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        exact (Nat.coprime_primes (ht p hp) (ht q hq)).mpr hpq
      rw [f, ite_eq_left ⟨hodd, hsf⟩, Nat.primeFactors_prod ht]
      apply prod_congr rfl
      intro p hp
      have hgt : 2 < p := by
        have hp2 := (ht p hp).two_le
        have hne : p ≠ 2 := by
          intro he
          exact h2 (he ▸ hp)
        omega
      simp [w, hgt]
  have hdiv : ∑ n ∈ k.divisors, f n = ∑ n ∈ k.divisors with Squarefree n, f n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hs : Squarefree n
    · simp [hs]
    · simp [f, hs]
  have hp : prodFac k = ∏ p ∈ k.primeFactors, (1 + w p) := by
    unfold prodFac
    apply prod_congr rfl
    intro p hp
    dsimp only [w]
    split_ifs with hgt
    · have hne : (p : ℝ) - 2 ≠ 0 := by
        have hpr : (2 : ℝ) < p := by exact_mod_cast hgt
        linarith
      field_simp
      ring
    · norm_num
  rw [hp, prod_one_add, hdiv, Nat.sum_divisors_filter_squarefree hk, Nat.factors_eq]
  apply sum_congr rfl
  intro t ht
  symm
  rw [t.prod_val, Function.id_def]
  exact hfprod t (fun p hp => Nat.prime_of_mem_primeFactors ((mem_powerset.mp ht) hp))

/-- LEAF. Unit U-1555. Tao 2012, (4.17): for `n ≥ 1` and any `h'`,
`#{1 ≤ h ≤ H : 2n | h - h'} ≤ H/(2n) + 1`. -/
theorem count_multiples (H h' : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (((Icc 1 H).filter fun h : ℕ => (2 * (n : ℤ)) ∣ (h : ℤ) - h').card : ℝ) ≤
      H / (2 * n) + 1 := by
  classical
  let s := (Icc 1 H).filter fun h : ℕ => (2 * (n : ℤ)) ∣ (h : ℤ) - h'
  have hc : s.card ≤ (range (H / (2 * n) + 1)).card := by
    apply card_le_card_of_injOn (fun h => h / (2 * n))
    · intro h hh
      have hhH : h ≤ H := (mem_Icc.mp (mem_filter.mp hh).1).2
      simp only [mem_coe, mem_range, Nat.lt_succ_iff]
      exact Nat.div_le_div_right hhH
    · intro a ha b hb he
      dsimp only at he
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      have hma : Nat.ModEq (2 * n) a h' := by
        rw [Nat.modEq_iff_dvd]
        simpa using dvd_neg.mpr ha'
      have hmb : Nat.ModEq (2 * n) b h' := by
        rw [Nat.modEq_iff_dvd]
        simpa using dvd_neg.mpr hb'
      have hm : a % (2 * n) = b % (2 * n) := hma.trans hmb.symm
      have hqa := Nat.mod_add_div a (2 * n)
      have hqb := Nat.mod_add_div b (2 * n)
      rw [he, hm] at hqa
      omega
  simp only [card_range] at hc
  have hcr : (s.card : ℝ) ≤ (H / (2 * n) : ℕ) + 1 := by exact_mod_cast hc
  have hd : ((H / (2 * n) : ℕ) : ℝ) ≤ (H : ℝ) / (2 * n) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_div_le (m := H) (n := 2 * n) (α := ℝ))
  exact hcr.trans (by linarith)

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, the step after (4.16): inserting
the divisor identity and exchanging sums, since `f` lives on odd `n` and `h - h'` is even,
`G(h') ≤ ∑_{n ≤ H} f(n) #{1 ≤ h ≤ H : 2n | h - h'}` for `1 ≤ h' ≤ H`. -/
theorem swap_le {H h' : ℕ} (hh' : h' ∈ Icc 1 H) :
    G H h' ≤ ∑ n ∈ Icc 1 H,
      f n * (((Icc 1 H).filter fun h : ℕ => (2 * (n : ℤ)) ∣ (h : ℤ) - h').card : ℝ) := by
  classical
  have hR : (∑ n ∈ Icc 1 H,
      f n * (((Icc 1 H).filter fun h : ℕ => (2 * (n : ℤ)) ∣ (h : ℤ) - h').card : ℝ)) =
      ∑ h ∈ Icc 1 H, ∑ n ∈ Icc 1 H, if (2 * (n : ℤ)) ∣ (h : ℤ) - h' then f n else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro n hn
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul]
    ring
  rw [hR]
  have hrow {h : ℕ} (hh : h ∈ (Icc 1 H).erase h') :
      (if Even ((h : ℤ) - h') then prodFac ((h : ℤ) - h').natAbs else 0) ≤
        ∑ n ∈ Icc 1 H, if (2 * (n : ℤ)) ∣ (h : ℤ) - h' then f n else 0 := by
    have hne := ne_of_mem_erase hh
    have hhH := mem_Icc.mp (mem_of_mem_erase hh)
    have hh'H := mem_Icc.mp hh'
    have hk : ((h : ℤ) - h') ≠ 0 := by omega
    have hkpos : 0 < ((h : ℤ) - h').natAbs := Int.natAbs_pos.mpr hk
    have hkH : ((h : ℤ) - h').natAbs ≤ H := by
      have habs : |((h : ℤ) - h')| ≤ (H : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
      rw [← Int.natCast_natAbs] at habs
      exact_mod_cast habs
    have hsub : ((h : ℤ) - h').natAbs.divisors ⊆ Icc 1 H := by
      intro n hn
      have hd := Nat.dvd_of_mem_divisors hn
      have hnle := Nat.le_of_dvd hkpos hd
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hn, hnle.trans hkH⟩
    split_ifs with he
    · rw [prodFac_eq_divsum hkpos.ne']
      have hterm {n : ℕ} (hn : n ∈ ((h : ℤ) - h').natAbs.divisors) :
          f n ≤ if (2 * (n : ℤ)) ∣ (h : ℤ) - h' then f n else 0 := by
        by_cases hf : f n = 0
        · simp [hf]
        have hodd : Odd n := by
          by_contra ho
          exact hf (by simp [f, ho])
        have hn : n ∣ ((h : ℤ) - h').natAbs := Nat.dvd_of_mem_divisors hn
        have h2 : 2 ∣ ((h : ℤ) - h').natAbs := he.natAbs.two_dvd
        have hmul : 2 * n ∣ ((h : ℤ) - h').natAbs := hodd.coprime_two_left.mul_dvd_of_dvd_of_dvd h2 hn
        have hzi : (2 * (n : ℤ)) ∣ (h : ℤ) - h' := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using Int.natCast_dvd.mpr hmul
        simp [hzi]
      have h1 := sum_le_sum (fun n hn => hterm hn)
      have h2 := sum_le_sum_of_subset_of_nonneg (f := fun (n : ℕ) => if (2 * (n : ℤ)) ∣ (h : ℤ) - h' then f n else 0)
        hsub (fun n _ _ => by split_ifs <;> first | exact le_refl 0 | exact f_nonneg n)
      exact h1.trans h2
    · exact sum_nonneg (fun n hn => by split_ifs <;> first | exact le_refl 0 | exact f_nonneg n)
  have h1 := sum_le_sum (fun h hh => hrow hh)
  have h2 := sum_le_sum_of_subset_of_nonneg (f := fun (h : ℕ) => ∑ n ∈ Icc 1 H,
      if (2 * (n : ℤ)) ∣ (h : ℤ) - h' then f n else 0)
    (erase_subset h' (Icc 1 H))
    (fun h _ _ => sum_nonneg (fun n hn => by split_ifs <;> first | exact le_refl 0 | exact f_nonneg n))
  exact h1.trans h2

/-- Tao 2012, page 22, proof of Proposition 4.10. Removing factors from the
positive twin prime product gives an upper bound by the corresponding finite product. -/
theorem twinConst_le_finite (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    twinConst ≤ 2 * ∏ p ∈ s, (if 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1) := by
  classical
  let u : Nat.Primes → ℝ := fun p => if 2 < (p : ℕ) then -(1 / ((p : ℝ) - 1)^2) else 0
  have hbase : Summable (fun p : Nat.Primes => (4 : ℝ) * ((p : ℝ) ^ 2)⁻¹) := by
    exact ((Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4).subtype _
  have hbound (p : Nat.Primes) : ‖u p‖ ≤ 4 * ((p : ℝ) ^ 2)⁻¹ := by
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
    simp only [u]
    split_ifs with h2
    · generalize hcast : (p : ℝ) = P at hp ⊢
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      rw [← one_div, mul_one_div, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    · simp only [norm_zero]
      positivity
  have hsum : Summable (fun p => ‖u p‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hbase
  have hp (p : Nat.Primes) : 0 < 1 + u p := by
    simp only [u]
    split_ifs with h2
    · have hp : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ (p : ℕ))
      have hdiv : (1 : ℝ) / ((p : ℝ) - 1)^2 < 1 := by
        rw [div_lt_one (by nlinarith)]
        nlinarith
      linarith
    · norm_num
  have hm := multipliable_one_add_of_summable hsum
  let e : {p : ℕ // p ∈ s} ↪ Nat.Primes :=
    ⟨fun p => ⟨p, by exact hs p p.property⟩,
      by intro a b hab; apply Subtype.ext; exact congrArg (fun p : Nat.Primes => (p : ℕ)) hab⟩
  let sp := s.attach.map e
  have hp1 (p : Nat.Primes) : 1 + u p ≤ 1 := by
    simp only [u]
    split_ifs <;> linarith [show 0 ≤ (1 : ℝ) / ((p : ℝ) - 1)^2 by positivity]
  have htotal : (∏' p, (1 + u p)) ≤ ∏ p ∈ sp, (1 + u p) := by
    apply le_of_tendsto hm.hasProd
    exact Filter.eventually_atTop.2 ⟨sp, fun t hst =>
      prod_le_prod_of_subset_of_le_one₀ hst (fun p _ => (hp p).le) (fun p _ _ => hp1 p)⟩
  have hprod : (∏ p ∈ sp, (1 + u p)) =
      ∏ p ∈ s, (if 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1) := by
    simp only [sp, prod_map]
    rw [← prod_attach s (fun p => (if 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1))]
    apply prod_congr rfl
    intro p hp'
    change 1 + (if 2 < (p : ℕ) then -(1 / (((p : ℕ) : ℝ) - 1)^2) else 0) =
      (if 2 < (p : ℕ) then 1 - 1 / (((p : ℕ) : ℝ) - 1)^2 else 1)
    split_ifs <;> ring
  have ht : twinConst = 2 * ∏' p, (1 + u p) := by
    unfold twinConst
    congr 1
    apply tprod_congr
    intro p
    simp only [u]
    split_ifs <;> ring
  rw [ht]
  exact (mul_le_mul_of_nonneg_left htotal (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by rw [hprod])

/-- LEAF. Unit U-1555. Tao 2012, Section 4: the twin prime constant
`𝔖₂ = 2 ∏_{p>2} (1 - 1/(p-1)²)` is positive. -/
theorem twinConst_pos : 0 < twinConst := by
  let u : Nat.Primes → ℝ := fun p => if 2 < (p : ℕ) then -(1 / ((p : ℝ) - 1)^2) else 0
  have hbase : Summable (fun p : Nat.Primes => (4 : ℝ) * ((p : ℝ) ^ 2)⁻¹) := by
    exact ((Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4).subtype _
  have hbound (p : Nat.Primes) : ‖u p‖ ≤ 4 * ((p : ℝ) ^ 2)⁻¹ := by
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
    simp only [u]
    split_ifs with h2
    · generalize hcast : (p : ℝ) = P at hp ⊢
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      rw [← one_div, mul_one_div, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    · simp only [norm_zero]
      positivity
  have hs : Summable (fun p => ‖u p‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hbase
  have hp (p : Nat.Primes) : 0 < 1 + u p := by
    simp only [u]
    split_ifs with h2
    · have hp : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ (p : ℕ))
      have hdiv : (1 : ℝ) / ((p : ℝ) - 1)^2 < 1 := by
        rw [div_lt_one (by nlinarith)]
        nlinarith
      linarith
    · norm_num
  have hn : (∏' p, (1 + u p)) ≠ 0 := tprod_one_add_ne_zero_of_summable (fun p => (hp p).ne') hs
  have hnn : 0 ≤ ∏' p, (1 + u p) := tprod_nonneg (fun p => (hp p).le)
  have ht : twinConst = 2 * ∏' p, (1 + u p) := by
    unfold twinConst
    congr 1
    apply tprod_congr
    intro p
    simp only [u]
    split_ifs <;> ring
  rw [ht]
  exact mul_pos (by norm_num) (lt_of_le_of_ne hnn (Ne.symm hn))

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, the Euler product step in its
corrected form `∑_n f(n)/(2n) = (1/2) ∏_{p>2} (1 + f(p)/p) = 1/𝔖₂`; here the partial sums:
`∑_{n ≤ N} f(n)/(2n) ≤ 1/𝔖₂`. -/
theorem f_euler_partial (N : ℕ) : ∑ n ∈ Icc 1 N, f n / (2 * n) ≤ 1 / twinConst := by
  classical
  let w : ℕ → ℝ := fun p => if 2 < p then 1 / ((p : ℝ) - 2) else 0
  have hfprod (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
      f (∏ p ∈ t, p) = ∏ p ∈ t, w p := by
    by_cases h2 : 2 ∈ t
    · have hd : 2 ∣ ∏ p ∈ t, p := dvd_prod_of_mem _ h2
      have hodd : ¬ Odd (∏ p ∈ t, p) := fun ho => ho.not_two_dvd_nat hd
      have hf0 : f (∏ p ∈ t, p) = 0 := by simp [f, hodd]
      rw [hf0]
      symm
      apply prod_eq_zero h2
      simp [w]
    · have hodd : Odd (∏ p ∈ t, p) := by
        apply Nat.coprime_two_right.mp
        apply Nat.Coprime.prod_left
        intro p hp
        exact Nat.coprime_two_right.mpr ((ht p hp).odd_of_ne_two (by intro he; exact h2 (he ▸ hp)))
      have hsf : Squarefree (∏ p ∈ t, p) := by
        refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
          (fun p hp => (ht p hp).squarefree)
        change IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        exact (Nat.coprime_primes (ht p hp) (ht q hq)).mpr hpq
      rw [f, ite_eq_left ⟨hodd, hsf⟩, Nat.primeFactors_prod ht]
      apply prod_congr rfl
      intro p hp
      have hgt : 2 < p := by
        have hp2 := (ht p hp).two_le
        have hne : p ≠ 2 := by
          intro he
          exact h2 (he ▸ hp)
        omega
      simp [w, hgt]
  let Q := primorial N
  have hQ0 : Q ≠ 0 := (primorial_pos N).ne'
  have hQsf : Squarefree Q := squarefree_primorial N
  have hfilter : (∑ n ∈ Icc 1 N, f n / (n : ℝ)) =
      ∑ n ∈ (Icc 1 N).filter Squarefree, f n / (n : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hs : Squarefree n
    · simp [hs]
    · simp [f, hs]
  have hsub : (Icc 1 N).filter Squarefree ⊆ Q.divisors := by
    intro n hn
    have hs := (mem_filter.mp hn).2
    have hnN := (mem_Icc.mp (mem_filter.mp hn).1).2
    exact Nat.mem_divisors.mpr ⟨hs.dvd_primorial.trans (primorial_dvd_primorial hnN), hQ0⟩
  have hsumQ : (∑ n ∈ Q.divisors, f n / (n : ℝ)) =
      ∏ p ∈ Q.primeFactors, (1 + w p / (p : ℝ)) := by
    rw [← Nat.divisors_filter_squarefree_of_squarefree hQsf,
      Nat.sum_divisors_filter_squarefree hQ0, Nat.factors_eq, prod_one_add]
    apply sum_congr rfl
    intro t ht
    have htprime : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors ((mem_powerset.mp ht) hp)
    rw [t.prod_val, Function.id_def, hfprod t htprime, Nat.cast_prod, ← prod_div_distrib]
  let A : ℕ → ℝ := fun p => if 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1
  have hEuler : (∏ p ∈ Q.primeFactors, (1 + w p / (p : ℝ))) =
      1 / ∏ p ∈ Q.primeFactors, A p := by
    rw [one_div, ← prod_inv_distrib]
    apply prod_congr rfl
    intro p hp
    simp only [w, A]
    split_ifs with hgt
    · have hpR : (2 : ℝ) < p := by exact_mod_cast hgt
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hfac : 1 - 1 / ((p : ℝ) - 1)^2 =
          (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)^2 := by
        field_simp
        ring
      rw [hfac, inv_div]
      field_simp
      ring
    · simp
  have hpartial : (∑ n ∈ Icc 1 N, f n / (n : ℝ)) ≤ 1 / ∏ p ∈ Q.primeFactors, A p := by
    rw [hfilter]
    calc _ ≤ ∑ n ∈ Q.divisors, f n / (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => div_nonneg (f_nonneg n) (Nat.cast_nonneg n))
      _ = _ := by rw [hsumQ, hEuler]
  have heq : (∑ n ∈ Icc 1 N, f n / (2 * n)) = (1 / 2 : ℝ) * ∑ n ∈ Icc 1 N, f n / (n : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
    field_simp
  rw [heq]
  have hc := twinConst_le_finite Q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  change twinConst ≤ 2 * ∏ p ∈ Q.primeFactors, A p at hc
  have hApos : 0 < ∏ p ∈ Q.primeFactors, A p := by nlinarith [twinConst_pos]
  calc _ ≤ (1 / 2 : ℝ) * (1 / ∏ p ∈ Q.primeFactors, A p) :=
      mul_le_mul_of_nonneg_left hpartial (by norm_num)
    _ = 1 / (2 * ∏ p ∈ Q.primeFactors, A p) := by field_simp
    _ ≤ 1 / twinConst := one_div_le_one_div_of_le twinConst_pos hc

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10: for odd `n`,
`f(n) = 1_{(n,2)=1} (μ²(n)/φ(n)) (2n/φ(2n)) (1/2) ∏_{p | n, p>2} (1 - 1/(p-1)²)^{-1}`, and the
last factor is at most `1/𝔖₂`, so `𝔖₂ f(n) ≤ (2n/φ(2n)) μ²(n)/φ(n)`. -/
theorem f_le_phi {n : ℕ} (hn : Odd n) :
    twinConst * f n ≤ ((2 * n : ℕ) : ℝ) / Nat.totient (2 * n) * muPhi n := by
  classical
  by_cases hsf : Squarefree n
  · have h3 {p : ℕ} (hp : p ∈ n.primeFactors) : 2 < p := by
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hne : p ≠ 2 := by
        intro he
        exact hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors hp)
      have := hprime.two_le
      omega
    have hphi : (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
      rw [Nat.totient_eq_div_primeFactors_mul n, Nat.prod_primeFactors_of_squarefree hsf,
        Nat.div_self (Nat.pos_of_ne_zero hsf.ne_zero), one_mul, Nat.cast_prod]
      apply prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (by have := h3 hp; omega : 1 ≤ p)]
      simp
    have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
    have hprod : (∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1)^2)) *
        (∏ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2)) = (n : ℝ) / (Nat.totient n : ℝ)^2 := by
      rw [hphi, hnprod, ← prod_pow, ← prod_div_distrib, ← prod_mul_distrib]
      apply prod_congr rfl
      intro p hp
      have hpr : (2 : ℝ) < p := by exact_mod_cast h3 hp
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
      field_simp
      ring
    have hc := twinConst_le_finite n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    have hfin : (∏ p ∈ n.primeFactors, (if 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1)) =
        ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1)^2) := by
      apply prod_congr rfl
      intro p hp
      rw [ite_eq_left (h3 hp)]
    rw [hfin] at hc
    have hf : f n = ∏ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2) := by simp [f, hn, hsf]
    have hmu : ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    have hphi0 : (Nat.totient n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hsf.ne_zero)).ne'
    calc twinConst * f n ≤ (2 * ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1)^2)) * f n :=
        mul_le_mul_of_nonneg_right hc (f_nonneg n)
      _ = 2 * ((n : ℝ) / (Nat.totient n : ℝ)^2) := by rw [hf, mul_assoc, hprod]
      _ = _ := by
        unfold muPhi
        rw [Nat.totient_two_mul_of_odd hn, hmu]
        push_cast
        field_simp
  · simp [f, hsf, muPhi, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10: `L ↦ e^γ L + 2.507/L` is
increasing on `L ≥ 1.19`, since `e^γ > 1.781 > 2.507/1.19²`; this moves `log log 2n` up to
`log log 2H`. -/
theorem gRS_mono {a b : ℝ} (ha : 1.19 ≤ a) (hab : a ≤ b) : gRS a ≤ gRS b := by
  have hγ : (0.573 : ℝ) < eulerMascheroniConstant := by
    have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 127
    have hlog : log (128 : ℝ) = 7 * log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    norm_num [Real.eulerMascheroniSeq, harmonic, Finset.sum_range_succ] at hseq
    rw [hlog] at hseq
    linarith [Real.log_two_lt_d9]
  have he : (1.772 : ℝ) ≤ exp eulerMascheroniConstant := by
    have hs := Real.sum_le_exp_of_nonneg (x := 0.573) (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at hs
    have hm := Real.exp_le_exp.mpr hγ.le
    linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have habprod : (1.19 : ℝ)^2 ≤ a * b := by nlinarith
  have heprod : (2.507 : ℝ) ≤ exp eulerMascheroniConstant * (a * b) := by
    nlinarith
  unfold gRS
  have hd : 2.507 / a - 2.507 / b = 2.507 * (b - a) / (a * b) := by field_simp
  have hbound : 2.507 * (b - a) / (a * b) ≤ exp eulerMascheroniConstant * (b - a) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr heprod)]
  linarith

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, the constant `2.507` covers the
exception of Rosser and Schoenfeld's Theorem 15: for `n = 223092870 = 2·3·5·7·11·13·17·19·23`,
`n/φ(n) ≤ e^γ log log n + 2.507 / log log n`; numerically `6.11291 ≤ 6.11312`. -/
theorem rs_exception :
    (223092870 : ℝ) / Nat.totient 223092870 ≤ gRS (log (log 223092870)) := by
  have hphi : Nat.totient 223092870 = 36495360 := by
    have he : (223092870 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 := by norm_num
    rw [he]
    rw [Nat.totient_mul (show Nat.Coprime (2 * 3 * 5 * 7 * 11 * 13 * 17 * 19) 23 from by decide)]
    rw [Nat.totient_mul (show Nat.Coprime (2 * 3 * 5 * 7 * 11 * 13 * 17) 19 from by decide)]
    rw [Nat.totient_mul (show Nat.Coprime (2 * 3 * 5 * 7 * 11 * 13) 17 from by decide)]
    rw [Nat.totient_mul (show Nat.Coprime (2 * 3 * 5 * 7 * 11) 13 from by decide)]
    rw [Nat.totient_mul (show Nat.Coprime (2 * 3 * 5 * 7) 11 from by decide)]
    rw [Nat.totient_mul (show Nat.Coprime (2 * 3 * 5) 7 from by decide)]
    rw [Nat.totient_mul (show Nat.Coprime (2 * 3) 5 from by decide)]
    rw [Nat.totient_mul (show Nat.Coprime (2) 3 from by decide)]
    norm_num [Nat.totient_prime]
  have hL : (2.9561 : ℝ) ≤ log (log 223092870) := by
    have hlog : (19.223 : ℝ) ≤ log 223092870 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have hex : exp (0.223 : ℝ) ≤ 1.2499 := by
        have ht := Real.exp_bound' (x := 0.223) (n := 8) (by norm_num) (by norm_num) (by norm_num)
        norm_num [sum_range_succ, Nat.factorial] at ht
        linarith
      have he : exp (19.223 : ℝ) = exp 1 ^ 19 * exp 0.223 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        norm_num
      rw [he]
      have hm := mul_le_mul (pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 19) hex
        (exp_pos _).le (by positivity)
      exact hm.trans (by norm_num)
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    apply le_trans _ hlog
    have hx : exp (0.9561 : ℝ) ≤ 2.601531 := by
      have ht := Real.exp_bound' (x := 0.9561) (n := 14) (by norm_num) (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at ht
      linarith
    have he : exp (2.9561 : ℝ) = exp 1 ^ 2 * exp 0.9561 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    rw [he]
    have hm := mul_le_mul (pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 2) hx
      (exp_pos _).le (by positivity)
    exact hm.trans (by norm_num)
  have hg : (1.78104 : ℝ) ≤ exp eulerMascheroniConstant := by
    have hs := Real.sum_le_exp_of_nonneg (x := 0.57720) (by norm_num) 10
    norm_num [sum_range_succ, Nat.factorial] at hs
    have he := Real.exp_le_exp.mpr LeanLab.ChenExplicit.Gamma.gamma_gt.le
    linarith
  have hm := gRS_mono (a := 2.9561) (by norm_num) hL
  unfold gRS at hm
  rw [hphi]
  have hb : (223092870 : ℝ) / 36495360 ≤ exp eulerMascheroniConstant * 2.9561 + 2.507 / 2.9561 := by
    norm_num
    linarith
  simpa only [gRS, Nat.cast_ofNat] using hb.trans hm

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, the small cases checked by hand:
for `1 ≤ m < 27` and `H ≥ 100`, `m/φ(m) ≤ e^γ log log 2H + 2.507/log log 2H`; the left side is
at most 3 and the right side at least 4.4. -/
theorem small_m {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 27) {H : ℝ} (hH : 100 ≤ H) :
    (m : ℝ) / Nat.totient m ≤ gRS (log (log (2 * H))) := by
  have hm3 : (m : ℝ) / Nat.totient m ≤ 3 := by
    have hnat : m ≤ 3 * Nat.totient m := by interval_cases m <;> decide
    have hpos : (0 : ℝ) < Nat.totient m := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < m))
    apply (div_le_iff₀ hpos).mpr
    exact_mod_cast hnat
  have hlog : 1 < log (2 * H) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL : 0 < log (log (2 * H)) := Real.log_pos hlog
  have he : (1.5 : ℝ) ≤ exp eulerMascheroniConstant := by
    have := Real.add_one_le_exp eulerMascheroniConstant
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  apply hm3.trans
  unfold gRS
  have hs := sq_nonneg (log (log (2 * H)) - 1)
  have hd : 3 - exp eulerMascheroniConstant * log (log (2 * H)) ≤
      2.507 / log (log (2 * H)) := by
    apply (le_div_iff₀ hL).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (sq_nonneg (log (log (2 * H))))]
  linarith

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, numerical: `log log 27 ≥ 1.19`,
so Rosser and Schoenfeld's range `m ≥ 27` lies where `gRS` increases; `log log 27 ≈ 1.1927`. -/
theorem loglog27 : (1.19 : ℝ) ≤ log (log 27) := by
  have h27 : (3.2958 : ℝ) ≤ log 27 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    have := Real.log_three_gt_d9
    norm_num at *
    linarith
  have he19 : exp (0.19 : ℝ) ≤ 1.21 := by
    have h := Real.exp_bound' (x := 0.19) (n := 3) (by norm_num) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have he : exp (1.19 : ℝ) ≤ 3.2958 := by
    rw [show (1.19 : ℝ) = 1 + 0.19 by norm_num, Real.exp_add]
    have h := mul_le_mul (Real.exp_one_lt_d9.le) he19 (Real.exp_pos _).le (by norm_num)
    linarith
  exact (Real.le_log_iff_exp_le (by linarith)).mpr (he.trans h27)

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10: `φ(n) = φ(2n)` and
`μ²(2n) = μ²(n)` for odd `n`, so
`∑_{n ≤ H, (n,2)=1} μ²(n)/φ(n) ≤ (1/2) ∑_{n ≤ 2H} μ²(n)/φ(n)`. -/
theorem sum_odd_half (H : ℕ) :
    ∑ n ∈ (Icc 1 H).filter Odd, muPhi n ≤ (1 / 2) * ∑ n ∈ Icc 1 (2 * H), muPhi n := by
  classical
  have hdouble (n : ℕ) (hn : Odd n) : muPhi (2 * n) = muPhi n := by
    unfold muPhi
    rw [Nat.totient_two_mul_of_odd hn,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hn.coprime_two_left]
    have hmu2 : μ 2 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime Nat.prime_two
    simp [hmu2]
  let s := (Icc 1 H).filter Odd
  have hdisj : Disjoint s (s.image (2 * ·)) := by
    apply disjoint_left.mpr
    intro n hn him
    obtain ⟨m, hm, rfl⟩ := mem_image.mp him
    have hodd := (mem_filter.mp hn).2
    obtain ⟨j, hj⟩ := hodd
    omega
  have hsub : s ∪ s.image (2 * ·) ⊆ Icc 1 (2 * H) := by
    intro n hn
    rcases mem_union.mp hn with hn | hn
    · have := mem_Icc.mp (mem_filter.mp hn).1
      exact mem_Icc.mpr ⟨this.1, by omega⟩
    · obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      have := mem_Icc.mp (mem_filter.mp hm).1
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : ∑ n ∈ s.image (2 * ·), muPhi n = ∑ n ∈ s, muPhi n := by
    rw [sum_image]
    · apply sum_congr rfl
      intro n hn
      exact hdouble n (mem_filter.mp hn).2
    · intro a ha b hb hab
      dsimp only at hab
      omega
  have hle := sum_le_sum_of_subset_of_nonneg (f := muPhi) hsub (fun n _ _ => by unfold muPhi; positivity)
  rw [sum_union hdisj, hsum] at hle
  linarith

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, last line of the second term:
`log(2H) + 1.4709 ≤ log(9H)`, as `log 4.5 > 1.504`. -/
theorem log_9H {H : ℝ} (hH : 0 < H) : log (2 * H) + 1.4709 ≤ log (9 * H) := by
  rw [Real.log_mul (by norm_num) hH.ne', Real.log_mul (by norm_num) hH.ne']
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h9]
  linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]

/-! ## Proved helpers and assemblies -/

/-- `muPhi n ≥ 0`. Proved. -/
theorem muPhi_nonneg (n : ℕ) : 0 ≤ muPhi n := by
  unfold muPhi; positivity

/-- `2n/φ(2n) ≤ e^γ log log 2H + 2.507/log log 2H` for odd `1 ≤ n ≤ H`, `H ≥ 100`, step 11 of
the proof of Proposition 4.10. CONDITIONAL ON the cited `rosser_schoenfeld_15` and the leaves
`rs_exception`, `gRS_mono`, `small_m`, `loglog27`. -/
theorem two_n_phi_le {n : ℕ} (hn1 : 1 ≤ n) {H : ℕ} (hnH : n ≤ H) (hH : 100 ≤ H) :
    ((2 * n : ℕ) : ℝ) / Nat.totient (2 * n) ≤ gRS (log (log (2 * (H : ℝ)))) := by
  have hHr : (100 : ℝ) ≤ H := by exact_mod_cast hH
  set m := 2 * n with hm
  rcases lt_or_ge m 27 with hsmall | hbig
  · exact small_m (by omega) hsmall hHr
  · have hm27 : (27 : ℝ) ≤ m := by exact_mod_cast hbig
    have hm2H : (m : ℝ) ≤ 2 * (H : ℝ) := by
      have : m ≤ 2 * H := by omega
      exact_mod_cast this
    have hlog27 : 3 < log (27 : ℝ) := by
      have := Real.add_one_lt_exp (by norm_num : (3 : ℝ) ≠ 0)
      have h20 : exp 3 < 27 := by
        have := Real.exp_one_lt_d9
        have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [h3]
        have h0 : 0 ≤ exp 1 := (Real.exp_pos 1).le
        calc exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ h0 this.le 3
          _ < 27 := by norm_num
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact h20
    have hlm : log (27 : ℝ) ≤ log m := Real.log_le_log (by norm_num) hm27
    have hL1 : 1.19 ≤ log (log (m : ℝ)) :=
      loglog27.trans (Real.log_le_log (by linarith) hlm)
    have hL2 : log (log (m : ℝ)) ≤ log (log (2 * (H : ℝ))) := by
      apply Real.log_le_log (by linarith)
      exact Real.log_le_log (by linarith) hm2H
    have hmono := gRS_mono hL1 hL2
    have hpt : (m : ℝ) / Nat.totient m ≤ gRS (log (log (m : ℝ))) := by
      by_cases hex : m = 223092870
      · rw [hex]; push_cast; exact rs_exception
      · have h15 := rosser_schoenfeld_15 (by omega : 3 ≤ m) hex
        have hLpos : 0 < log (log (m : ℝ)) := by linarith
        have : 2.50637 / log (log (m : ℝ)) ≤ 2.507 / log (log (m : ℝ)) :=
          div_le_div_of_nonneg_right (by norm_num) hLpos.le
        unfold gRS; linarith
    exact hpt.trans hmono

/-- The second term of the off-diagonal bound, steps 10 to 13 of the proof of Proposition 4.10:
`𝔖₂ ∑_{n ≤ H} f(n) ≤ (e^γ log log 2H + 2.507/log log 2H) log(9H)/2` for `H ≥ 100`.
CONDITIONAL ON the leaves `f_le_phi`, `sum_odd_half`, `log_9H`, those of `two_n_phi_le`, and
the cited `ramare_mu_phi`. -/
theorem second_term_le {H : ℕ} (hH : 100 ≤ H) :
    twinConst * ∑ n ∈ Icc 1 H, f n ≤ gRS (log (log (2 * (H : ℝ)))) * log (9 * H) / 2 := by
  set g := gRS (log (log (2 * (H : ℝ))))
  have hHr : (100 : ℝ) ≤ H := by exact_mod_cast hH
  have hg : 0 ≤ g := by
    have h1 : (0 : ℝ) ≤ (1 : ℕ) / Nat.totient 1 := by norm_num
    exact h1.trans (by simpa using small_m (m := 1) le_rfl (by norm_num) hHr)
  have hpt : ∀ n ∈ Icc 1 H, twinConst * f n ≤ if Odd n then g * muPhi n else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    split_ifs with hodd
    · have h1 := f_le_phi hodd
      have h2 := two_n_phi_le hn.1 hn.2 hH
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (muPhi_nonneg n))
    · have : f n = 0 := by
        unfold f; split_ifs with hc
        · exact absurd hc.1 hodd
        · rfl
      simp [this]
  have hsum : twinConst * ∑ n ∈ Icc 1 H, f n ≤ g * ∑ n ∈ (Icc 1 H).filter Odd, muPhi n := by
    rw [mul_sum, mul_sum, sum_filter]
    exact sum_le_sum fun n hn => by
      have := hpt n hn
      split_ifs at this ⊢ with h
      · exact this
      · exact this
  have hodd := sum_odd_half H
  have h2H : 1 ≤ 2 * H := by omega
  have hR := ramare_mu_phi h2H
  have hl9 := log_9H (by linarith : (0 : ℝ) < H)
  have hcast : ((2 * H : ℕ) : ℝ) = 2 * (H : ℝ) := by push_cast; ring
  rw [hcast] at hR
  calc twinConst * ∑ n ∈ Icc 1 H, f n ≤ g * ∑ n ∈ (Icc 1 H).filter Odd, muPhi n := hsum
    _ ≤ g * ((1 / 2) * (log (2 * (H : ℝ)) + 1.4709)) :=
        mul_le_mul_of_nonneg_left (hodd.trans (by linarith)) hg
    _ ≤ g * ((1 / 2) * log (9 * H)) :=
        mul_le_mul_of_nonneg_left (by linarith) hg
    _ = g * log (9 * H) / 2 := by ring

/-- For each `1 ≤ h' ≤ H`: `G(h') ≤ H/𝔖₂ + ∑_{n ≤ H} f(n)`, steps 6 to 9 of the proof of
Proposition 4.10. CONDITIONAL ON the leaves `swap_le`, `count_multiples`, `f_euler_partial`. -/
theorem G_le {H h' : ℕ} (hh' : h' ∈ Icc 1 H) :
    G H h' ≤ H / twinConst + ∑ n ∈ Icc 1 H, f n := by
  have h1 := swap_le hh'
  have hHr : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have h2 : ∀ n ∈ Icc 1 H,
      f n * (((Icc 1 H).filter fun h : ℕ => (2 * (n : ℤ)) ∣ (h : ℤ) - h').card : ℝ) ≤
        H * (f n / (2 * n)) + f n := by
    intro n hn
    rw [mem_Icc] at hn
    have hc := count_multiples H h' hn.1
    have := mul_le_mul_of_nonneg_left hc (f_nonneg n)
    calc _ ≤ f n * (H / (2 * n) + 1) := this
      _ = H * (f n / (2 * n)) + f n := by ring
  have h3 := sum_le_sum h2
  rw [sum_add_distrib, ← mul_sum] at h3
  have h4 := f_euler_partial H
  have h5 : (H : ℝ) * ∑ n ∈ Icc 1 H, f n / (2 * n) ≤ H * (1 / twinConst) :=
    mul_le_mul_of_nonneg_left h4 hHr
  calc G H h' ≤ _ := h1
    _ ≤ _ := h3
    _ ≤ H * (1 / twinConst) + ∑ n ∈ Icc 1 H, f n := by linarith
    _ = H / twinConst + ∑ n ∈ Icc 1 H, f n := by ring

end LeanLab.Tao2012.Decomp1555
