/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". This file proves the statement of `leaf_rough_interval_density` of
`LowerPrincipal517f`, the Buchstab local density of the rough cofactor `n3` or `n5` of display
5.15, uniformly in the level, by induction on the number of prime factors:

* `buchstab_main_term`: the recursion for the main terms alone, from the prime number theorem
  step `prime_weight_transfer` and the two halves `buchstab_telescope` and `lattice_abel` of the
  Buchstab identity for densities;
* `rough_density_strip`: the induction through the finite Buchstab identity `rough_sum_decomp`;
* `rough_interval_density`: the target statement.

Nothing is left open in this file. No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.RoughDensity517d

namespace LeanLab.BHP1997.LowerShortC165
open Classical
open scoped BigOperators
open LeanLab.BHP1997.Task308 (roughIndicator)

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
main term only. With no rough number left: the Buchstab density sum at level `z` over `(a, b]`
equals the number of primes `p ≥ z` in `(a, b]` plus the sum over primes `p ≥ z` of the
Buchstab density sums at level `p` over the cofactor range `(a / p, b / p]`, cofactor above
`1`, with every log power saved. Assembled from `prime_weight_transfer`, the prime number
theorem in the prime `p`, and `buchstab_telescope` with `lattice_abel`, the integral equation
`u ω(u) = 1 + ∫_1^{u-1} ω` in summed form. -/
theorem buchstab_main_term (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)| ≤
          C * b * Real.log X ^ (-A) := by
  obtain ⟨CA, hCA, hA'⟩ := prime_weight_transfer ω hω hz hc A hA
  obtain ⟨C1, hC1, h1'⟩ := buchstab_telescope ω hω hz hc A hA
  obtain ⟨C2, hC2, h2'⟩ := lattice_abel ω hω hz hc A hA
  refine ⟨CA + C1 + C2, by positivity, fun X hX z hzX a b ha hb => ?_⟩
  have hAb := hA' X (by linarith) z hzX a b ha hb
  have h1 := h1' X (by linarith) z hzX a b ha hb
  have h2 := h2' X (by linarith) z hzX a b ha hb
  have hid : ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        (if a < k then (1 : ℝ) else 0) / Real.log k := by
    have hI : Finset.Ioc a b = (Finset.Icc 1 b).filter (fun k => a < k) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : a < k <;> by_cases h2 : z ≤ k <;> simp [h1, h2]
  have e1 : ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)) =
      ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := Finset.sum_add_distrib
  have e2 : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        ((if a < k then (1 : ℝ) else 0) +
          ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (if a < k then (1 : ℝ) else 0) / Real.log k +
        ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k := by
    simp only [add_div, Finset.sum_add_distrib]
  rw [e1, hid] at h1
  rw [e2] at hAb
  obtain ⟨hA1, hA2⟩ := abs_le.mp hAb
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  obtain ⟨h21, h22⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- P0069 page 51, display 5.17, the induction on the number of prime factors: the Buchstab
local density of the integers of `(a, b]` free of prime factors below `z ≥ X ^ c`, for
`b < z ^ (k + 1)`, so that such an integer has at most `k` prime factors. The step applies the
case `k` at each level `p ≥ z` to the cofactors and uses `buchstab_main_term`. -/
theorem rough_density_strip (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (k : ℕ) : ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X → b < z ^ (k + 1) →
        |∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.log X ^ (-A) := by
  induction k with
  | zero =>
    intro A hA
    refine ⟨1, one_pos, fun X hX z _ a b ha _ hbz => ?_⟩
    rw [zero_add, pow_one] at hbz
    have hzero : ∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
        ω (Real.log n / Real.log z) / Real.log z) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
      have hnz : n < z := lt_of_le_of_lt hnb hbz
      have hr : roughIndicator n z = 0 := by
        unfold roughIndicator
        rw [ite_eq_right]
        rintro (h | h)
        · omega
        · have := Nat.minFac_le (by omega : 0 < n)
          omega
      have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnz)
      rw [hr, hz _ hu]
      simp
    rw [hzero, abs_zero]
    have := Real.rpow_nonneg (Real.log_nonneg hX) (-A)
    positivity
  | succ k ih =>
    intro A hA
    obtain ⟨C1, hC1, h1⟩ := ih (A + 1) (by linarith)
    obtain ⟨C2, hC2, h2⟩ := buchstab_main_term ω hω hz hc A hA
    refine ⟨max (max C1 C2) 3 + 2 * C1 + C2, by positivity, fun X hX z hzX a b ha hb hbz => ?_⟩
    have hm3 : (3 : ℝ) ≤ max (max C1 C2) 3 := le_max_right _ _
    have hm1 : C1 ≤ max (max C1 C2) 3 := (le_max_left _ _).trans (le_max_left _ _)
    have hm2 : C2 ≤ max (max C1 C2) 3 := (le_max_right _ _).trans (le_max_left _ _)
    have hX1 : C1 ≤ X := by linarith
    have hX2 : C2 ≤ X := by linarith
    have hX3 : 3 ≤ X := by linarith
    have hlog1 : 1 ≤ Real.log X :=
      (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
    have hlog0 : 0 < Real.log X := by linarith
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hpow : Real.log X ^ (-(A + 1)) * Real.log X = Real.log X ^ (-A) := by
      rw [← Real.rpow_add_one hlog0.ne']
      congr 1
      ring
    have hL0 : 0 ≤ Real.log X ^ (-(A + 1)) := Real.rpow_nonneg hlog0.le _
    have hsplit : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        ∑ m ∈ Finset.Ioc (a / p) (b / p), roughIndicator m p =
          (if a < p then (1 : ℝ) else 0) +
            ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p), roughIndicator m p := by
      intro p hp
      obtain ⟨hpI, hpp, -⟩ := Finset.mem_filter.mp hp
      rw [cofactor_one_split hpp.two_le (Finset.mem_Icc.mp hpI).2 (fun m => roughIndicator m p)]
      simp [roughIndicator]
    have key : ∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z) =
        ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
          ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p) -
        (∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)) := by
      rw [Finset.sum_sub_distrib, rough_sum_decomp z a b ha, Finset.sum_congr rfl hsplit]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    have hinner : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        |∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| ≤
          C1 * b * Real.log X ^ (-(A + 1)) * (p : ℝ)⁻¹ := by
      intro p hp
      obtain ⟨hpI, hpp, hzp⟩ := Finset.mem_filter.mp hp
      have hp0 : 0 < p := hpp.pos
      have hbp : b / p < p ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]
        exact lt_of_lt_of_le hbz (Nat.pow_le_pow_left hzp _)
      have hcast : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) / p := Nat.cast_div_le
      have hbpX : ((b / p : ℕ) : ℝ) ≤ X :=
        le_trans (by exact_mod_cast Nat.div_le_self b p) hb
      have h := h1 X hX1 p (hzX.trans (by exact_mod_cast hzp)) (max (a / p) 1) (b / p)
        (le_max_right _ _) hbpX hbp
      calc _ ≤ C1 * ((b / p : ℕ) : ℝ) * Real.log X ^ (-(A + 1)) := h
        _ ≤ C1 * ((b : ℝ) / p) * Real.log X ^ (-(A + 1)) := by gcongr
        _ = _ := by rw [div_eq_mul_inv]; ring
    have hharm : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
        2 * Real.log X := by
      have hs : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
          ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
      have hh : ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ = (harmonic b : ℝ) := by
        simp [harmonic_eq_sum_Icc]
      have hl : Real.log b ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0
          simpa using hlog0.le
        · exact Real.log_le_log (by exact_mod_cast h0) hb
      have := harmonic_le_one_add_log b
      linarith
    have hleaf := h2 X hX2 z hzX a b ha hb
    rw [key]
    calc _ ≤ |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| +
            C2 * b * Real.log X ^ (-A) := (abs_sub _ _).trans (by gcongr)
      _ ≤ ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              C1 * b * Real.log X ^ (-(A + 1)) * (p : ℝ)⁻¹ + C2 * b * Real.log X ^ (-A) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hinner)
      _ ≤ C1 * b * Real.log X ^ (-(A + 1)) * (2 * Real.log X) + C2 * b * Real.log X ^ (-A) := by
          rw [← Finset.mul_sum]
          gcongr
      _ = (2 * C1 + C2) * b * Real.log X ^ (-A) := by rw [← hpow]; ring
      _ ≤ (max (max C1 C2) 3 + 2 * C1 + C2) * b * Real.log X ^ (-A) := by
          have := Real.rpow_nonneg hlog0.le (-A)
          gcongr
          linarith

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
applied to the rough variable `n3` or `n5` of display 5.15, page 50. The integers of an interval
`(a, b]` with no prime factor below `z`, where `z ≥ X ^ c` and `b ≤ X`, have local density
`ω(log n / log z) / log z` with every log power saved. Proved from `rough_density_strip` with
`k` past `1 / c`. This is the statement of `leaf_rough_interval_density` of `LowerPrincipal517f`. -/
theorem rough_interval_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.log X ^ (-A) := by
  obtain ⟨C, hC, h⟩ := rough_density_strip ω hω hz hc ⌈1 / c⌉₊ A hA
  refine ⟨C + 2, by linarith, fun X hX z hzX a b ha hb => ?_⟩
  have hX1 : 1 < X := by linarith
  have hk : 1 < c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ) := by
    have h1 : 1 / c ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hc] at h1
    push_cast
    nlinarith
  have hbz : b < z ^ (⌈1 / c⌉₊ + 1) := by
    have h3 : X < (z : ℝ) ^ (⌈1 / c⌉₊ + 1) := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ < X ^ (c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt hX1 hk
        _ = (X ^ c) ^ (⌈1 / c⌉₊ + 1) := by
            rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
        _ ≤ (z : ℝ) ^ (⌈1 / c⌉₊ + 1) :=
            pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hzX _
    exact_mod_cast lt_of_le_of_lt hb h3
  have hlog := Real.rpow_nonneg (Real.log_nonneg hX1.le) (-A)
  calc _ ≤ C * b * Real.log X ^ (-A) := h X (by linarith) z hzX a b ha hb hbz
    _ ≤ (C + 2) * b * Real.log X ^ (-A) := by
        have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
        gcongr
        linarith

end LeanLab.BHP1997.LowerShortC165
