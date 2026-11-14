/-
P0069 pages 26 and 27, display 4.13. CODEX task528 continuation.
Outer factor counting for the actual intermediate divisor band.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp528f
import LeanLab.BHP1997.EnergyLogC165

namespace LeanLab.BHP1997.Decomp528g
open Classical DecompC165b Decomp528a Decomp528e Decomp528f Decomp312c
open scoped BigOperators

/-- Page 26 display 4.7, the divisor-indexed convolution equals the same sum
on the fixed dyadic factor ranges at every positive index. -/
theorem finiteConvolution_eq_dyadic {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (a b r : ℕ → ℝ) {k : ℕ} (hk : k ≠ 0) :
    finiteConvolution M N a b r k =
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        if m * n ∣ k then a m * b n * r (k / (m * n)) else 0 := by
  have hmem {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
      j ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊ ↔ R < j ∧ (j : ℝ) ≤ 2 * R := by
    constructor
    · intro hj
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hj
      exact ⟨(Nat.floor_lt hR).mp hlo,
        (Nat.cast_le.mpr hhi).trans (Nat.floor_le (by linarith))⟩
    · rintro ⟨hlo, hhi⟩
      exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hR).mpr hlo, Nat.le_floor hhi⟩
  rw [finiteConvolution, ← Finset.sum_product', ← Finset.sum_product']
  apply Finset.sum_congr_of_eq_on_inter
  · intro p hp hnot
    split_ifs with h
    · obtain ⟨hm, hm', hn, hn', hd⟩ := h
      exact False.elim (hnot (Finset.mem_product.mpr
        ⟨(hmem hM p.1).mpr ⟨hm, hm'⟩, (hmem hN p.2).mpr ⟨hn, hn'⟩⟩))
    · rfl
  · intro p hp hnot
    split_ifs with h
    · have hm : p.1 ∣ k := (dvd_mul_right p.1 p.2).trans h
      have hn : p.2 ∣ k := (dvd_mul_left p.2 p.1).trans h
      exact False.elim (hnot (Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hm, hk⟩, Nat.mem_divisors.mpr ⟨hn, hk⟩⟩))
    · rfl
  · intro p hp hp'
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hp'
    obtain ⟨hm, hm'⟩ := (hmem hM p.1).mp hm
    obtain ⟨hn, hn'⟩ := (hmem hN p.2).mp hn
    simp only [hm, hm', hn, hn', true_and]

/-- Pages 26 and 27, the intermediate band is the exact finite sum of divisor incidences.
This copies the reusable gcd step already used locally in Decomp528f. -/
theorem roughBand_eq_sum (n : ℕ) (z γ : ℝ) :
    roughBand n z γ =
      ∑ d ∈ (Thm2.primorialBelow z).divisors.filter
        (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z),
        if d ∣ n then (1 : ℝ) else 0 := by
  let P := Thm2.primorialBelow z
  let D := P.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z)
  have hP : P ≠ 0 := (primorial_squarefree z).ne_zero
  have hg : Nat.gcd n P ≠ 0 := by
    intro h
    exact hP (Nat.gcd_eq_zero_iff.mp h).2
  have he : (Nat.gcd n P).divisors.filter
      (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z) = D.filter (fun d => d ∣ n) := by
    ext d
    simp only [D, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, hg, hP,
      ne_eq, not_false_eq_true, and_true]
    tauto
  change (((Nat.gcd n P).divisors.filter
    (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z)).card : ℝ) = _
  rw [he]
  simp only [Finset.sum_boole, D, P]

/-- Page 27 display 4.13, the complete weighted band is an exact triple incidence sum. -/
theorem bandConvolution_eq_sum {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (a b : ℕ → ℝ) (z γ : ℝ) {k : ℕ} (hk : k ≠ 0) :
    bandConvolution M N a b z γ k =
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        ∑ d ∈ (Thm2.primorialBelow z).divisors.filter
          (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z),
          if m * n * d ∣ k then |a m| * |b n| else 0 := by
  rw [bandConvolution, finiteConvolution_eq_dyadic hM hN _ _ _ hk]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m * n ∣ k
  · rw [if_pos hmn, roughBand_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ k / (m * n)
    · have hh : m * n * d ∣ k := (Nat.dvd_div_iff_mul_dvd hmn).mp hdv
      simp only [if_pos hdv, if_pos hh, mul_one]
    · have hh : ¬m * n * d ∣ k := by
        intro hh
        exact hdv ((Nat.dvd_div_iff_mul_dvd hmn).mpr hh)
      simp only [if_neg hdv, if_neg hh, mul_zero]
  · rw [if_neg hmn]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have hh : ¬m * n * d ∣ k := by
      intro hh
      exact hmn ((dvd_mul_right (m * n) d).trans hh)
    simp only [if_neg hh]

/-- Page 27 display 4.13, weighted product incidences are bounded by interval length
and one endpoint error for every outer factor and divisor triple. -/
theorem weighted_product_incidence_le (S T D : Finset ℕ)
    (hS : ∀ m ∈ S, 0 < m) (hT : ∀ n ∈ T, 0 < n) (hD : ∀ d ∈ D, 0 < d)
    (a b : ℕ → ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, ∑ m ∈ S, ∑ n ∈ T, ∑ d ∈ D,
      if m * n * d ∣ k then |a m| * |b n| else 0) ≤
      (v - u) * (∑ m ∈ S, |a m| / (m : ℝ)) * (∑ n ∈ T, |b n| / (n : ℝ)) *
        (∑ d ∈ D, 1 / (d : ℝ)) +
      (D.card : ℝ) * (∑ m ∈ S, |a m|) * (∑ n ∈ T, |b n|) := by
  have hprod (f g h : ℕ → ℝ) :
      (∑ m ∈ S, ∑ n ∈ T, ∑ d ∈ D, f m * g n * h d) =
        (∑ m ∈ S, f m) * (∑ n ∈ T, g n) * (∑ d ∈ D, h d) := by
    symm
    rw [Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
  have ht (m n d : ℕ) :
      |a m| * |b n| * ((v - u) / ((m * n * d : ℕ) : ℝ) + 1) =
        ((v - u) * (|a m| / (m : ℝ))) * (|b n| / (n : ℝ)) * (1 / (d : ℝ)) +
          |a m| * |b n| := by
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    _ = ∑ m ∈ S, ∑ n ∈ T, ∑ d ∈ D, ∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        if m * n * d ∣ k then |a m| * |b n| else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ ≤ ∑ m ∈ S, ∑ n ∈ T, ∑ d ∈ D,
        |a m| * |b n| * ((v - u) / ((m * n * d : ℕ) : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro d hd
      have he : (∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
          if m * n * d ∣ k then |a m| * |b n| else 0) =
          |a m| * |b n| * (((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter
            (fun k => m * n * d ∣ k)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_left
        (interval_multiples_card_le hu huv (Nat.mul_pos (Nat.mul_pos (hS m hm) (hT n hn))
          (hD d hd))) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ m ∈ S, ∑ n ∈ T, ∑ d ∈ D,
          ((v - u) * (|a m| / (m : ℝ))) * (|b n| / (n : ℝ)) * (1 / (d : ℝ))) +
        (∑ m ∈ S, ∑ n ∈ T, ∑ d ∈ D, |a m| * |b n| * 1) := by
      simp_rw [ht, Finset.sum_add_distrib, mul_one]
    _ = ((∑ m ∈ S, (v - u) * (|a m| / (m : ℝ))) *
          (∑ n ∈ T, |b n| / (n : ℝ)) * (∑ d ∈ D, 1 / (d : ℝ))) +
        ((∑ m ∈ S, |a m|) * (∑ n ∈ T, |b n|) * (∑ _d ∈ D, (1 : ℝ))) := by
      rw [hprod, hprod]
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
      ring

/-- Page 27 display 4.13, the full existing band sum with both outer factor weights.
The endpoint term is kept explicitly before the reference interval asymptotics. -/
theorem bandConvolution_interval_le {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (a b : ℕ → ℝ) (z γ : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, bandConvolution M N a b z γ k) ≤
      (v - u) * (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |a m| / (m : ℝ)) *
        (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |b n| / (n : ℝ)) *
        (∑ d ∈ (Thm2.primorialBelow z).divisors.filter
          (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ)) +
      (⌈γ * z⌉₊ : ℝ) * (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |a m|) *
        (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |b n|) := by
  let S := Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊
  let T := Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊
  let D := (Thm2.primorialBelow z).divisors.filter
    (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z)
  have hS (m : ℕ) (hm : m ∈ S) : 0 < m := by
    have h := (Finset.mem_Ioc.mp hm).1
    omega
  have hT (n : ℕ) (hn : n ∈ T) : 0 < n := by
    have h := (Finset.mem_Ioc.mp hn).1
    omega
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d :=
    Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hcard : (D.card : ℝ) ≤ (⌈γ * z⌉₊ : ℝ) := by
    have hsub : D ⊆ Finset.range ⌈γ * z⌉₊ := by
      intro d hd
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (Finset.mem_filter.mp hd).2.2)
    exact_mod_cast (show D.card ≤ ⌈γ * z⌉₊ from by
      simpa only [Finset.card_range] using Finset.card_le_card hsub)
  have hrecip : (∑ d ∈ D, 1 / (d : ℝ)) ≤
      ∑ d ∈ (Thm2.primorialBelow z).divisors.filter
        (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2.1⟩
    · intro d hd hnot
      positivity
  calc
    _ = ∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, ∑ m ∈ S, ∑ n ∈ T, ∑ d ∈ D,
        if m * n * d ∣ k then |a m| * |b n| else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact bandConvolution_eq_sum hM hN a b z γ (by
        have h := (Finset.mem_Ioc.mp hk).1
        omega)
    _ ≤ (v - u) * (∑ m ∈ S, |a m| / (m : ℝ)) * (∑ n ∈ T, |b n| / (n : ℝ)) *
        (∑ d ∈ D, 1 / (d : ℝ)) + (D.card : ℝ) * (∑ m ∈ S, |a m|) *
          (∑ n ∈ T, |b n|) := weighted_product_incidence_le S T D hS hT hD a b hu huv
    _ ≤ _ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hrecip (by
          apply mul_nonneg
          · exact mul_nonneg (sub_nonneg.mpr huv) (Finset.sum_nonneg fun _ _ => by positivity)
          · exact Finset.sum_nonneg fun _ _ => by positivity)
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _))

/-- Page 12 divisor moments and page 27 display 4.13.
A divisor-bounded real coefficient has a logarithmic harmonic majorant. -/
theorem coefficient_harmonic_le (a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ n, |a n| ≤ (n.divisors.card : ℝ) ^ B) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, |a n| / (n : ℝ)) ≤
      (1 + Real.log N) ^ (2 ^ ⌈B⌉₊) := by
  calc
    _ ≤ EnergyLogC165.harmonicDivisorMoment ⌈B⌉₊ N := by
      unfold EnergyLogC165.harmonicDivisorMoment
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := by
        have h := (Finset.mem_Icc.mp hn).1
        omega
      have hτ : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
      have hp : (n.divisors.card : ℝ) ^ B ≤ (n.divisors.card : ℝ) ^ ⌈B⌉₊ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hτ (Nat.le_ceil B)
      exact div_le_div_of_nonneg_right ((ha n).trans hp) (Nat.cast_nonneg n)
    _ ≤ _ := EnergyLogC165.harmonicDivisorMoment_le _ _

/-- Page 27 display 4.13, reciprocal and ordinary dyadic coefficient sums
are controlled by the same elementary harmonic divisor moment. -/
theorem dyadic_coefficient_sums_le {M : ℝ} (hM : 0 ≤ M) (a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ n, |a n| ≤ (n.divisors.card : ℝ) ^ B) :
    (∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |a n| / (n : ℝ)) ≤
        (1 + Real.log ⌊2 * M⌋₊) ^ (2 ^ ⌈B⌉₊) ∧
    (∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |a n|) ≤
        2 * M * (1 + Real.log ⌊2 * M⌋₊) ^ (2 ^ ⌈B⌉₊) := by
  let S := Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊
  have hS : S ⊆ Finset.Icc 1 ⌊2 * M⌋₊ := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hharm : (∑ n ∈ S, |a n| / (n : ℝ)) ≤
      (1 + Real.log ⌊2 * M⌋₊) ^ (2 ^ ⌈B⌉₊) := by
    apply le_trans ?_ (coefficient_harmonic_le a B ha ⌊2 * M⌋₊)
    exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
  refine ⟨hharm, ?_⟩
  calc
    _ ≤ 2 * M * (∑ n ∈ S, |a n| / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (Finset.mem_Icc.mp (hS hn)).1
      have hnup : (n : ℝ) ≤ 2 * M :=
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le (by positivity))
      calc
        |a n| = (n : ℝ) * (|a n| / (n : ℝ)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hnup (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hharm (by positivity)

/-- Page 27 display 4.13, the factor coefficient majorants are uniform in every
length between one and x once log x is at least one. -/
theorem dyadic_coefficient_sums_log {x M : ℝ} (hx : 2 ≤ x) (hlog : 1 ≤ Real.log x)
    (hM : 1 ≤ M) (hMx : M ≤ x) (a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ n, |a n| ≤ (n.divisors.card : ℝ) ^ B) :
    (∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |a n| / (n : ℝ)) ≤
        (3 * Real.log x) ^ (2 ^ ⌈B⌉₊) ∧
    (∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |a n|) ≤
        2 * M * (3 * Real.log x) ^ (2 ^ ⌈B⌉₊) := by
  have hx0 : 0 < x := by linarith
  have hfloor : 1 ≤ ⌊2 * M⌋₊ := Nat.le_floor (by norm_num <;> linarith)
  have hfpos : (0 : ℝ) < ⌊2 * M⌋₊ := by exact_mod_cast hfloor
  have hlf : Real.log ⌊2 * M⌋₊ ≤ Real.log (2 * x) :=
    Real.log_le_log hfpos ((Nat.floor_le (by linarith : 0 ≤ 2 * M)).trans (by linarith))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hlf
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hb : 1 + Real.log ⌊2 * M⌋₊ ≤ 3 * Real.log x := by linarith
  have hp : (1 + Real.log ⌊2 * M⌋₊) ^ (2 ^ ⌈B⌉₊) ≤
      (3 * Real.log x) ^ (2 ^ ⌈B⌉₊) := by
    apply pow_le_pow_left₀ (by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ ⌊2 * M⌋₊ by exact_mod_cast hfloor)
      linarith) hb
  obtain ⟨h1, h2⟩ := dyadic_coefficient_sums_le (show 0 ≤ M by linarith) a B ha
  exact ⟨h1.trans hp, h2.trans (mul_le_mul_of_nonneg_left hp (by positivity))⟩

/-- Pages 25 to 27, the endpoint count at the paper cutoffs costs only gamma
times an arbitrarily small fixed power of x. -/
theorem paper_cutoff_rounding {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (⌈x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ : ℝ) ≤
        2 * x ^ (ε / 12 + δ) := by
  filter_upwards [roughness_eventually_le_power hδ,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hw hx1
  have hx0 : 0 < x := by linarith
  have hprod : x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤
      x ^ (ε / 12 + δ) := by
    calc
      _ ≤ x ^ (ε / 12) * x ^ δ := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := (Real.rpow_add hx0 _ _).symm
  have hc := Nat.ceil_lt_add_one (show
      0 ≤ x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ)) by positivity)
  have hp : 1 ≤ x ^ (ε / 12 + δ) := Real.one_le_rpow hx1 (by positivity)
  linarith

/-- Page 24, reference width, and page 27, display 4.13. Any fixed
sublinear power with a logarithmic factor is absorbed by the reference width. -/
theorem referenceWidth_absorbs_power_log {ρ : ℝ} (hρ : ρ < 1) (D A C : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |C| * x ^ ρ * Real.log x ^ D ≤ referenceWidth x * Real.log x ^ (-A) := by
  let β : ℝ := (1 + ρ) / 2
  have hβ : β < 1 := by dsimp [β]; linarith
  have hgap : 0 < β - ρ := by dsimp [β]; linarith
  have hl := ((isLittleO_log_rpow_rpow_atTop (D + A) hgap).const_mul_left |C|).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [referenceWidth_eventually_ge_power hβ, hl,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hw hl hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hb : |C| * Real.log x ^ (D + A) ≤ x ^ (β - ρ) := by
    simpa only [norm_mul, Real.norm_eq_abs, abs_abs,
      abs_of_nonneg (Real.rpow_nonneg hL.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hl
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).2
  calc
    _ = x ^ ρ * (|C| * Real.log x ^ (D + A)) := by
      rw [Real.rpow_add hL]; ring
    _ ≤ x ^ ρ * x ^ (β - ρ) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = x ^ β := by rw [← Real.rpow_add hx0]; congr 1; ring
    _ ≤ _ := hw

/-- Page 27 display 4.13 with both divisor-bounded outer coefficient sums
estimated uniformly. The endpoint term is still explicit. -/
theorem bandConvolution_interval_log_le {x M N u v : ℝ}
    (hx : 2 ≤ x) (hlog : 1 ≤ Real.log x)
    (hM : 1 ≤ M) (hMx : M ≤ x) (hN : 1 ≤ N) (hNx : N ≤ x)
    (a b : ℕ → ℝ) (B : ℝ)
    (ha : ∀ k, |a k| ≤ (k.divisors.card : ℝ) ^ B)
    (hb : ∀ k, |b k| ≤ (k.divisors.card : ℝ) ^ B)
    (z γ : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    (∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, bandConvolution M N a b z γ k) ≤
      (v - u) * (3 * Real.log x) ^ (2 * (2 ^ ⌈B⌉₊)) *
        (∑ d ∈ (Thm2.primorialBelow z).divisors.filter
          (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ)) +
      4 * (⌈γ * z⌉₊ : ℝ) * M * N * (3 * Real.log x) ^ (2 * (2 ^ ⌈B⌉₊)) := by
  obtain ⟨ha1, ha2⟩ := dyadic_coefficient_sums_log hx hlog hM hMx a B ha
  obtain ⟨hb1, hb2⟩ := dyadic_coefficient_sums_log hx hlog hN hNx b B hb
  have hH : 0 ≤ (3 * Real.log x) ^ (2 ^ ⌈B⌉₊) := by positivity
  have hab1 := mul_le_mul ha1 hb1 (Finset.sum_nonneg fun _ _ => by positivity) hH
  have hab2 := mul_le_mul ha2 hb2 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (show 0 ≤ 2 * M * (3 * Real.log x) ^ (2 ^ ⌈B⌉₊) by positivity)
  have hp : (3 * Real.log x) ^ (2 ^ ⌈B⌉₊) *
      (3 * Real.log x) ^ (2 ^ ⌈B⌉₊) =
      (3 * Real.log x) ^ (2 * (2 ^ ⌈B⌉₊)) := by rw [two_mul, pow_add]
  rw [hp] at hab1
  have hab2' : (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |a m|) *
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |b n|) ≤
      4 * M * N * (3 * Real.log x) ^ (2 * (2 ^ ⌈B⌉₊)) := by
    convert hab2 using 1 <;> rw [← hp] <;> ring
  refine (bandConvolution_interval_le (by linarith) (by linarith) a b z γ hu huv).trans ?_
  apply add_le_add
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hab1 (sub_nonneg.mpr huv))
      (show 0 ≤ ∑ d ∈ (Thm2.primorialBelow z).divisors.filter
        (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ) from
          Finset.sum_nonneg fun _ _ => by positivity)
  · have hc : 0 ≤ (⌈γ * z⌉₊ : ℝ) := by positivity
    convert mul_le_mul_of_nonneg_left hab2' hc using 1 <;> ring

/-- Pages 26 and 27 displays 4.12 and 4.13. The full reference band error
has every logarithmic saving, uniformly in both outer factor lengths. -/
theorem reference_band_uniform {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ + ε / 12 < 1) (B : ℝ) (A : ℝ) (hA : 0 < A) :
    ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ M N : ℝ,
      1 ≤ M → 1 ≤ N → M * N ≤ x ^ ρ → ∀ a b : ℕ → ℝ,
      (∀ k, |a k| ≤ (k.divisors.card : ℝ) ^ B) →
      (∀ k, |b k| ≤ (k.divisors.card : ℝ) ^ B) →
      (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        bandConvolution M N a b (Real.exp (Real.log x ^ (9 / 10 : ℝ)))
          (x ^ (ε / 12)) k) ≤ C * referenceWidth x * Real.log x ^ (-A) := by
  let q : ℕ := 2 * (2 ^ ⌈B⌉₊)
  let C₀ : ℝ := (3 : ℝ) ^ q
  let δ : ℝ := (1 - (ρ + ε / 12)) / 4
  let θ : ℝ := ρ + (ε / 12 + δ)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hθ : θ < 1 := by dsimp [θ, δ]; linarith
  have hT : 0 < A + (q : ℝ) := by positivity
  have he := referenceWidth_absorbs_power_log hθ (q : ℝ) A (8 * C₀)
  have ht := reciprocal_tail_every_log hε hT
  have hr := paper_cutoff_rounding hε.le hδ
  have hall : ∀ᶠ x : ℝ in Filter.atTop, ∀ M N : ℝ,
      1 ≤ M → 1 ≤ N → M * N ≤ x ^ ρ → ∀ a b : ℕ → ℝ,
      (∀ k, |a k| ≤ (k.divisors.card : ℝ) ^ B) →
      (∀ k, |b k| ≤ (k.divisors.card : ℝ) ^ B) →
      (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        bandConvolution M N a b (Real.exp (Real.log x ^ (9 / 10 : ℝ)))
          (x ^ (ε / 12)) k) ≤ (C₀ + 1) * referenceWidth x * Real.log x ^ (-A) := by
    filter_upwards [he, ht, hr, Filter.eventually_ge_atTop (3 : ℝ),
      Filter.eventually_ge_atTop (Real.exp 1)] with x he ht hr hx3 hxe
    intro M N hM hN hMN a b ha hb
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hL1 : 1 ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
    have hL : 0 < Real.log x := by linarith
    have hρ1 : ρ ≤ 1 := by linarith
    have hxp : x ^ ρ ≤ x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 hρ1
    have hMx : M ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ M) hN).trans
      (hMN.trans hxp)
    have hNx : N ≤ x := (le_mul_of_one_le_left (by linarith : 0 ≤ N) hM).trans
      (hMN.trans hxp)
    have hW : 0 ≤ referenceWidth x := (referenceWidth_pos hx0).le
    have hu : 0 ≤ x - referenceWidth x := by linarith [referenceWidth_lt_quarter hx3]
    have huv : x - referenceWidth x ≤ x := by linarith
    have hraw := bandConvolution_interval_log_le (by linarith : 2 ≤ x) hL1
      hM hMx hN hNx a b B ha hb (Real.exp (Real.log x ^ (9 / 10 : ℝ)))
      (x ^ (ε / 12)) hu huv
    have hpow : (3 * Real.log x) ^ q = C₀ * Real.log x ^ q := by
      dsimp [C₀]; rw [mul_pow]
    have hcancel : Real.log x ^ q * Real.log x ^ (-(A + (q : ℝ))) =
        Real.log x ^ (-A) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hL]
      congr 1; ring
    have hmain : referenceWidth x * (3 * Real.log x) ^ q *
        (∑ d ∈ (Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ)))).divisors.filter (fun d : ℕ => x ^ (ε / 12) ≤ (d : ℝ)), 1 / (d : ℝ)) ≤
        C₀ * referenceWidth x * Real.log x ^ (-A) := by
      calc
        _ ≤ referenceWidth x * (3 * Real.log x) ^ q *
            Real.log x ^ (-(A + (q : ℝ))) :=
          mul_le_mul_of_nonneg_left ht (mul_nonneg hW (by positivity))
        _ = _ := by
          rw [hpow]
          calc
            _ = C₀ * referenceWidth x *
              (Real.log x ^ q * Real.log x ^ (-(A + (q : ℝ)))) := by ring
            _ = _ := by rw [hcancel]
    have hC : 0 ≤ C₀ := by dsimp [C₀]; positivity
    have he' : 8 * C₀ * x ^ θ * Real.log x ^ q ≤
        referenceWidth x * Real.log x ^ (-A) := by
      simpa only [abs_of_nonneg (by positivity : 0 ≤ 8 * C₀), Real.rpow_natCast] using he
    have hend : 4 * (⌈x ^ (ε / 12) *
        Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ : ℝ) * M * N *
        (3 * Real.log x) ^ q ≤ referenceWidth x * Real.log x ^ (-A) := by
      calc
        _ ≤ 4 * (2 * x ^ (ε / 12 + δ)) * M * N * (3 * Real.log x) ^ q := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hr (by norm_num)) (by linarith))
                (by linarith)) (by positivity)
        _ = 8 * C₀ * (M * N) * x ^ (ε / 12 + δ) * Real.log x ^ q := by
          rw [hpow]; ring
        _ ≤ 8 * C₀ * x ^ ρ * x ^ (ε / 12 + δ) * Real.log x ^ q := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hMN (by positivity)) (by positivity))
              (by positivity)
        _ = 8 * C₀ * x ^ θ * Real.log x ^ q := by
          dsimp [θ]; rw [Real.rpow_add hx0 ρ (ε / 12 + δ)]; ring
        _ ≤ _ := he'
    change _ ≤ (C₀ + 1) * referenceWidth x * Real.log x ^ (-A)
    have hraw' : (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        bandConvolution M N a b (Real.exp (Real.log x ^ (9 / 10 : ℝ)))
          (x ^ (ε / 12)) k) ≤ referenceWidth x * (3 * Real.log x) ^ q *
        (∑ d ∈ (Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ)))).divisors.filter (fun d : ℕ => x ^ (ε / 12) ≤ (d : ℝ)), 1 / (d : ℝ)) +
        4 * (⌈x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ : ℝ) *
          M * N * (3 * Real.log x) ^ q := by
      simpa only [sub_sub_cancel] using hraw
    exact hraw'.trans ((add_le_add hmain hend).trans_eq (by ring))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hall
  exact ⟨C₀ + 1, X, hX⟩

/-- Pages 26 and 27, display 4.12, for the actual power-sized factor families. -/
theorem section4_reference_band_bound {ε m n : ℝ} (hε : 0 < ε)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hsize : m + n + ε / 12 < 1)
    (a b : ℝ → ℕ → ℝ) (B : ℝ)
    (ha : ∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B)
    (hb : ∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
      (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        bandConvolution (x ^ m) (x ^ n) (a x) (b x)
          (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12)) k) ≤
        C * referenceWidth x * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, X, hX⟩ := reference_band_uniform hε hsize B A hA
  refine ⟨C, max X 1, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  apply hX x ((le_max_left _ _).trans hx) (x ^ m) (x ^ n)
    (Real.one_le_rpow hx1 hm) (Real.one_le_rpow hx1 hn) _ (a x) (b x) (ha x) (hb x)
  exact le_of_eq (Real.rpow_add hx0 m n).symm

/-- Pages 26 and 27 displays 4.10 to 4.13. CONDITIONAL on the existing
mean value leaf, the raw reference density and the short band estimate.
The reference band hypothesis is now discharged by the full weighted count. -/
theorem section4Block_supply_reference_complete (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      (max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 ∨ max m n ≤ 0.46) →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
      ∀ u : ℝ,
        ReferenceDensity u (fun x k => finiteConvolution (x ^ m) (x ^ n) (a x) (b x)
          (fun l => siftedWeight l ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊) k) →
        (∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
          (∑ k ∈ leftInterval ε x, bandConvolution (x ^ m) (x ^ n) (a x) (b x)
            (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12)) k) ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) →
        (∀ x k, |section4Block ε m n a b x k| ≤ (k.divisors.card : ℝ) ^ (2 * B + 3)) ∧
        MeanValue41 ε (section4Block ε m n a b) ∧
        ReferenceDensity u (section4Block ε m n a b) ∧
        ShortApproximation ε
          (fun x k => finiteConvolution (x ^ m) (x ^ n) (a x) (b x)
            (fun l => siftedWeight l ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊) k)
          (section4Block ε m n a b) := by
  obtain ⟨η, hη, hs⟩ := section4Block_supply h4 B hB
  refine ⟨min η (1 / 10), lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη m n hm0 hn0 hgroup a b ha hb u hd hshort
  apply hs ε hε (hεη.trans_le (min_le_left _ _)) m n hm0 hn0 hgroup a b ha hb u hd hshort
  apply section4_reference_band_bound hε hm0 hn0 _ a b B ha hb
  have hεsmall : ε < 1 / 10 := hεη.trans_le (min_le_right _ _)
  rcases hgroup with hgroup | hgroup
  · have hm := le_max_right (0.45 : ℝ) m
    have hn := le_max_right (0.225 : ℝ) n
    linarith
  · have hm := le_max_left m n
    have hn := le_max_right m n
    linarith

/-- Pages 26 and 27 display 4.12 and page 33 reference density.
CONDITIONAL only on the raw sifted convolution density. The elementary
reference band estimate supplies the truncation error without a new input. -/
theorem section4Block_referenceDensity {ε m n u : ℝ} (hε : 0 < ε)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hsize : m + n + ε / 12 < 1)
    (a b : ℝ → ℕ → ℝ) (B : ℝ)
    (ha : ∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B)
    (hb : ∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B)
    (hd : ReferenceDensity u (fun x k => finiteConvolution (x ^ m) (x ^ n) (a x) (b x)
      (fun l => siftedWeight l ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊) k)) :
    ReferenceDensity u (section4Block ε m n a b) := by
  have hγ : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ^ (ε / 12) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    exact Real.one_le_rpow hx (by positivity)
  exact auxiliaryConvolution_referenceDensity _ _ _ _ a b hγ hd
    (section4_reference_band_bound hε hm hn hsize a b B ha hb)

/-- Page 26 grouping and display 4.11. The admissible grouping alone does
not force the elementary endpoint exponent below the short interval exponent.
This compares exponents only and does not refute the analytic estimate. -/
theorem grouping_short_count_obstruction :
    (max (0.45 : ℝ) 0.46 + max (0.225 : ℝ) 0.46 ≤ 0.775 ∨
      max (0.46 : ℝ) 0.46 ≤ 0.46) ∧
    (11 / 20 + (1 / 100 : ℝ)) < 0.46 + 0.46 + (1 / 100 : ℝ) / 12 := by
  norm_num

end LeanLab.BHP1997.Decomp528g
