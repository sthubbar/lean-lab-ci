/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the rough cofactor of display 5.15 the main term of that consequence is the
Buchstab identity for densities. This file proves its lattice half: for each level `k` the
products `k m` in `(a, b]` are equidistributed among the integers of `(a, b]` with weight
`1 / k`, against the slowly varying density `ω(log (n / k) / log k) / (k log^2 k)`, by partial
summation; `lattice_abel` is the summed form. Nothing is left open in this file.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.RoughDensity517
import LeanLab.BHP1997.RoughDensity517b

namespace LeanLab.BHP1997.LowerShortC165
open Classical
open scoped BigOperators
open LeanLab.ChenDoubleSieve.Wu04Functional

/-- P0069 page 51, display 5.17: partial summation on an integer interval `(a, b]`, real
valued form of `Decomp514Abel.finite_abel`. -/
theorem abel_Ioc (f g : ℕ → ℝ) (a : ℕ) : ∀ b : ℕ, a ≤ b →
    ∑ n ∈ Finset.Ioc a b, f n * g n = f b * ∑ n ∈ Finset.Ioc a b, g n -
      ∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) * ∑ n ∈ Finset.Ioc a i, g n := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, Finset.sum_Ioc_succ_top hab, Finset.sum_Ico_succ_top hab, ih]
    ring

/-- P0069 page 51, display 5.17: partial summation bound. Prefix sums of `g` bounded by `R`
give the weighted sum bounded by `R` times the end value plus the total variation of `f`. -/
theorem abel_Ioc_bound (f g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) {R : ℝ}
    (hR : ∀ i : ℕ, a ≤ i → i ≤ b → |∑ n ∈ Finset.Ioc a i, g n| ≤ R) :
    |∑ n ∈ Finset.Ioc a b, f n * g n| ≤
      (|f b| + ∑ i ∈ Finset.Ico a b, |f (i + 1) - f i|) * R := by
  rw [abel_Ioc f g a b hab]
  calc _ ≤ |f b * ∑ n ∈ Finset.Ioc a b, g n| +
        |∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) * ∑ n ∈ Finset.Ioc a i, g n| := abs_sub _ _
    _ ≤ |f b| * R + ∑ i ∈ Finset.Ico a b, |f (i + 1) - f i| * R := by
      refine add_le_add ?_ ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_))
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hR b hab le_rfl) (abs_nonneg _)
      · intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hR i h1 h2.le) (abs_nonneg _)
    _ = _ := by rw [add_mul, Finset.sum_mul]

/-- P0069 page 51, display 5.17: the multiples of `k` in an interval, counted with weight `k`,
differ from the number of integers of the interval by less than `k`. -/
theorem dvd_weight_prefix {k : ℕ} (hk : 1 ≤ k) (a i : ℕ) (hai : a ≤ i) :
    |∑ n ∈ Finset.Ioc a i, ((if k ∣ n then (k : ℝ) else 0) - 1)| ≤ k := by
  rw [Finset.sum_sub_distrib, sum_dvd_reindex_real hk a i (fun _ => (k : ℝ))]
  simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub (Nat.div_le_div_right hai), Nat.cast_sub hai]
  have e1 : ((i / k : ℕ) : ℝ) * k = i - ((i % k : ℕ) : ℝ) := by
    have h : ((k * (i / k) + i % k : ℕ) : ℝ) = i := by exact_mod_cast Nat.div_add_mod i k
    push_cast at h
    linarith
  have e2 : ((a / k : ℕ) : ℝ) * k = a - ((a % k : ℕ) : ℝ) := by
    have h : ((k * (a / k) + a % k : ℕ) : ℝ) = a := by exact_mod_cast Nat.div_add_mod a k
    push_cast at h
    linarith
  have h1 : ((i % k : ℕ) : ℝ) < k := by exact_mod_cast Nat.mod_lt i hk
  have h2 : ((a % k : ℕ) : ℝ) < k := by exact_mod_cast Nat.mod_lt a hk
  have h3 : (0 : ℝ) ≤ ((i % k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((a % k : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

/-- P0069 page 51, display 5.17, Buchstab function input: with the zero extension below one,
Buchstab's function is at most `1` in absolute value everywhere. -/
theorem abs_buchstab_le_one {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) (u : ℝ) :
    |ω u| ≤ 1 := by
  by_cases hu : u < 1
  · rw [hz u hu]
    simp
  · obtain ⟨h1, h2⟩ := buchstab_bounds hω (u := u) (le_of_not_gt hu)
    rw [abs_le]
    constructor <;> linarith

/-- P0069 page 51, display 5.17: the density `ω(log (n / k) / log k) / (k log^2 k)` of the
products `k m` near `n` varies slowly in `n`: one step of `n` changes it by at most
`1 / (n k)`, apart from the step onto `n = k^2`, where the zero extension ends. -/
theorem lattice_density_step {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k i : ℕ} (hk : 3 ≤ k) (hi : 1 ≤ i) :
    |ω (Real.log ((i + 1 : ℕ) : ℝ) / Real.log k - 1) / (k * Real.log k ^ 2) -
        ω (Real.log i / Real.log k - 1) / (k * Real.log k ^ 2)| ≤
      1 / ((i : ℝ) * k) + (if i + 1 = k ^ 2 then 1 / (k : ℝ) else 0) := by
  have hκ3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ0 : (0 : ℝ) < k := by linarith
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hl1 : 1 ≤ Real.log k :=
    (Real.le_log_iff_exp_le hκ0).mpr (by linarith [Real.exp_one_lt_d9])
  have hl0 : 0 < Real.log k := by linarith
  have hden : (k : ℝ) ≤ k * Real.log k ^ 2 := le_mul_of_one_le_right hκ0.le (by nlinarith)
  have hden0 : (0 : ℝ) < k * Real.log k ^ 2 := by positivity
  have hite : (0 : ℝ) ≤ (if i + 1 = k ^ 2 then 1 / (k : ℝ) else 0) := by
    split_ifs <;> positivity
  have hik : (0 : ℝ) ≤ 1 / ((i : ℝ) * k) := by positivity
  rw [← sub_div, abs_div, abs_of_pos hden0]
  by_cases h1 : k ^ 2 ≤ i
  · have h2l : 2 * Real.log k ≤ Real.log i := by
      have := Real.log_le_log (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)
        (by exact_mod_cast h1 : (k : ℝ) ^ 2 ≤ i)
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hu : 1 ≤ Real.log i / Real.log k - 1 := by
      have : 2 ≤ Real.log i / Real.log k := (le_div_iff₀ hl0).mpr h2l
      linarith
    have hstep : Real.log ((i + 1 : ℕ) : ℝ) - Real.log i ≤ 1 / (i : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hi1 hi0)
      rw [Real.log_div hi1.ne' hi0.ne'] at h
      have e : ((i + 1 : ℕ) : ℝ) / i - 1 = 1 / (i : ℝ) := by
        push_cast
        field_simp
        ring
      linarith
    have hmono : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_le_log hi0 (by push_cast; linarith)
    have huu : Real.log i / Real.log k - 1 ≤ Real.log ((i + 1 : ℕ) : ℝ) / Real.log k - 1 := by
      have := div_le_div_of_nonneg_right hmono hl0.le
      linarith
    have hlip := Decomp514a.two_density_buchstab_lipschitz hω hz hu huu
    have hdiff : Real.log ((i + 1 : ℕ) : ℝ) / Real.log k - 1 - (Real.log i / Real.log k - 1) ≤
        1 / (i : ℝ) := by
      have e : Real.log ((i + 1 : ℕ) : ℝ) / Real.log k - 1 - (Real.log i / Real.log k - 1) =
          (Real.log ((i + 1 : ℕ) : ℝ) - Real.log i) / Real.log k := by ring
      rw [e]
      exact (div_le_self (by linarith) hl1).trans hstep
    rw [abs_sub_comm] at hlip
    calc _ ≤ (1 / (i : ℝ)) / (k * Real.log k ^ 2) :=
          div_le_div_of_nonneg_right (hlip.trans hdiff) hden0.le
      _ ≤ (1 / (i : ℝ)) / k := div_le_div_of_nonneg_left (by positivity) hκ0 hden
      _ = 1 / ((i : ℝ) * k) := by rw [div_div]
      _ ≤ _ := by linarith
  · have hlow : Real.log i / Real.log k - 1 < 1 := by
      have h2l : Real.log i < 2 * Real.log k := by
        have := Real.log_lt_log hi0 (by exact_mod_cast (by omega : i < k ^ 2) : (i : ℝ) < (k : ℝ) ^ 2)
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have : Real.log i / Real.log k < 2 := (div_lt_iff₀ hl0).mpr h2l
      linarith
    rw [hz _ hlow, sub_zero]
    by_cases h2 : i + 1 = k ^ 2
    · rw [ite_eq_left h2]
      calc _ ≤ 1 / (k * Real.log k ^ 2) :=
            div_le_div_of_nonneg_right (abs_buchstab_le_one hω hz _) hden0.le
        _ ≤ 1 / (k : ℝ) := one_div_le_one_div_of_le hκ0 hden
        _ ≤ _ := by linarith
    · have hlow' : Real.log ((i + 1 : ℕ) : ℝ) / Real.log k - 1 < 1 := by
        have h2l : Real.log ((i + 1 : ℕ) : ℝ) < 2 * Real.log k := by
          have := Real.log_lt_log hi1
            (by exact_mod_cast (by omega : i + 1 < k ^ 2) : ((i + 1 : ℕ) : ℝ) < (k : ℝ) ^ 2)
          rw [Real.log_pow] at this
          push_cast at this ⊢
          linarith
        have : Real.log ((i + 1 : ℕ) : ℝ) / Real.log k < 2 := (div_lt_iff₀ hl0).mpr h2l
        linarith
      rw [hz _ hlow', abs_zero, zero_div]
      linarith

/-- P0069 page 51, display 5.17: for one level `k`, the density
`ω(log (n / k) / log k) / (k log^2 k)` summed over the multiples of `k` in `(a, b]` with weight
`k` differs from its sum over all integers of `(a, b]` by at most `3 + log b`, by partial
summation. -/
theorem lattice_level_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k a b : ℕ} (hk : 3 ≤ k) (ha : 1 ≤ a) (hab : a ≤ b) :
    |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
        ((if k ∣ n then (k : ℝ) else 0) - 1)| ≤ 3 + Real.log b := by
  have hκ3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ0 : (0 : ℝ) < k := by linarith
  have hl1 : 1 ≤ Real.log k :=
    (Real.le_log_iff_exp_le hκ0).mpr (by linarith [Real.exp_one_lt_d9])
  have hden : (k : ℝ) ≤ k * Real.log k ^ 2 := le_mul_of_one_le_right hκ0.le (by nlinarith)
  have hden0 : (0 : ℝ) < k * Real.log k ^ 2 := by positivity
  have habel := abel_Ioc_bound
    (fun n : ℕ => ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))
    (fun n : ℕ => (if k ∣ n then (k : ℝ) else 0) - 1) hab (R := k)
    (fun i hai _ => dvd_weight_prefix (by omega) a i hai)
  have hfb : |ω (Real.log b / Real.log k - 1) / (k * Real.log k ^ 2)| ≤ 1 / (k : ℝ) := by
    rw [abs_div, abs_of_pos hden0]
    calc _ ≤ 1 / (k * Real.log k ^ 2) :=
          div_le_div_of_nonneg_right (abs_buchstab_le_one hω hz _) hden0.le
      _ ≤ 1 / (k : ℝ) := one_div_le_one_div_of_le hκ0 hden
  have hk2 : ∃ q : ℕ, k ^ 2 = q + 1 := ⟨k ^ 2 - 1, by
    have : 0 < k ^ 2 := by positivity
    omega⟩
  obtain ⟨q, hq⟩ := hk2
  have hvar : ∑ i ∈ Finset.Ico a b,
      |ω (Real.log ((i + 1 : ℕ) : ℝ) / Real.log k - 1) / (k * Real.log k ^ 2) -
        ω (Real.log i / Real.log k - 1) / (k * Real.log k ^ 2)| ≤
      (1 / (k : ℝ)) * (1 + Real.log b) + 1 / (k : ℝ) := by
    calc _ ≤ ∑ i ∈ Finset.Ico a b,
          (1 / (k : ℝ) * ((i : ℝ))⁻¹ + (if i = q then 1 / (k : ℝ) else 0)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h := lattice_density_step hω hz hk
            (by have := (Finset.mem_Ico.mp hi).1; omega : 1 ≤ i)
          have e : (if i + 1 = k ^ 2 then 1 / (k : ℝ) else 0) =
              (if i = q then 1 / (k : ℝ) else 0) := by
            by_cases hh : i = q <;> simp [hh, hq]
          rw [e] at h
          have e2 : 1 / ((i : ℝ) * k) = 1 / (k : ℝ) * ((i : ℝ))⁻¹ := by
            rw [one_div, one_div, mul_inv, mul_comm]
          rw [e2] at h
          exact h
      _ = 1 / (k : ℝ) * ∑ i ∈ Finset.Ico a b, ((i : ℝ))⁻¹ +
          ∑ i ∈ Finset.Ico a b, (if i = q then 1 / (k : ℝ) else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by
          have hs : ∑ i ∈ Finset.Ico a b, ((i : ℝ))⁻¹ ≤ ∑ i ∈ Finset.Icc 1 b, ((i : ℝ))⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
              have := Finset.mem_Ico.mp hi
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (fun i _ _ => by positivity)
          have hh : ∑ i ∈ Finset.Icc 1 b, ((i : ℝ))⁻¹ = (harmonic b : ℝ) := by
            simp [harmonic_eq_sum_Icc]
          have hlog := harmonic_le_one_add_log b
          have h1 : ∑ i ∈ Finset.Ico a b, ((i : ℝ))⁻¹ ≤ 1 + Real.log b := by linarith
          have h2 : ∑ i ∈ Finset.Ico a b, (if i = q then 1 / (k : ℝ) else 0) ≤ 1 / (k : ℝ) := by
            rw [Finset.sum_ite_eq']
            split_ifs
            · exact le_rfl
            · positivity
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
  calc _ ≤ _ := habel
    _ ≤ (1 / (k : ℝ) + ((1 / (k : ℝ)) * (1 + Real.log b) + 1 / (k : ℝ))) * k :=
        mul_le_mul_of_nonneg_right (add_le_add hfb hvar) hκ0.le
    _ = 3 + Real.log b := by
        field_simp
        ring

/-- P0069 page 51, display 5.17: a level `z ≥ X ^ c` is at least `3` once `X ≥ 3 ^ (1 / c)`. -/
theorem three_le_level {c X : ℝ} (hc : 0 < c) (hXc : (3 : ℝ) ^ (1 / c) ≤ X) {z : ℕ}
    (hzX : X ^ c ≤ (z : ℝ)) : 3 ≤ z := by
  have h3z : (3 : ℝ) ≤ z := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  exact_mod_cast h3z

/-- P0069 page 51, display 5.17, the lattice half of the Buchstab identity for densities: the
sum over `n` in `(a, b]` and levels `z ≤ k < n` of `ω(log (n / k) / log k) / (k log^2 k)` is the
sum over levels `k ≥ z` of the Buchstab density sums at level `k` over the cofactors `m` in
`(a / k, b / k]`, divided by `log k`, with every log power saved. -/
theorem lattice_abel (ω : ℝ → ℝ) (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
            ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
              ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.log X ^ (-A) := by
  obtain ⟨K, hK, hKX⟩ := rpow_neg_le_log_rpow_neg hc (A := A + 1) (by linarith)
  refine ⟨max ((3 : ℝ) ^ (1 / c)) 3 + 8 * K, by positivity, fun X hX z hzX a b ha hb => ?_⟩
  have hX3 : 3 ≤ X := by linarith [le_max_right ((3 : ℝ) ^ (1 / c)) 3]
  have hXc : (3 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((3 : ℝ) ^ (1 / c)) 3]
  have hX0 : 0 < X := by linarith
  have hz3 : 3 ≤ z := three_le_level hc hXc hzX
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 < Real.log X := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hlogk : ∀ k : ℕ, 3 ≤ k → 1 ≤ Real.log k := by
    intro k hk
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have hswap : ∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), ∑ n ∈ Finset.Ioc a b,
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := by
    calc _ = ∑ n ∈ Finset.Ioc a b, ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_subset ?_ ?_
          · intro k hk
            have h1 := Finset.mem_Ico.mp hk
            have h2 := Finset.mem_Ioc.mp hn
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h1.1⟩
          · intro k hk hnot
            obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
            have hnk : n ≤ k := by
              by_contra h
              exact hnot (Finset.mem_Ico.mpr ⟨hzk, by omega⟩)
            have hn0 : (0 : ℝ) < n := by
              exact_mod_cast (by have := (Finset.mem_Ioc.mp hn).1; omega : 0 < n)
            have hl := hlogk k (by omega)
            have hu : Real.log n / Real.log k - 1 < 1 := by
              have h3 : Real.log n / Real.log k ≤ 1 :=
                (div_le_one (by linarith)).mpr (Real.log_le_log hn0 (by exact_mod_cast hnk))
              linarith
            rw [hz _ hu, zero_div]
      _ = _ := Finset.sum_comm
  have hlevel : ∀ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
      (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
          ω (Real.log m / Real.log k) / Real.log k) / Real.log k =
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) := by
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hkb : k ≤ b := (Finset.mem_Icc.mp hk1).2
    have hk3 : 3 ≤ k := by omega
    have hl := hlogk k hk3
    have hκ0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h1 : ∀ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) =
        if k ∣ n then ω (Real.log ((k * (n / k) : ℕ) : ℝ) / Real.log k - 1) /
          (k * Real.log k ^ 2) * k else 0 := by
      intro n _
      by_cases hd : k ∣ n
      · simp only [hd, ite_true]
        rw [Nat.mul_div_cancel' hd]
      · simp [hd]
    rw [Finset.sum_congr rfl h1, sum_dvd_reindex_real (by omega : 1 ≤ k) a b
      (fun m : ℕ => ω (Real.log ((k * m : ℕ) : ℝ) / Real.log k - 1) /
          (k * Real.log k ^ 2) * k),
      cofactor_one_split (by omega : 2 ≤ k) hkb]
    have h0 : ω (Real.log ((k * 1 : ℕ) : ℝ) / Real.log k - 1) / (k * Real.log k ^ 2) * k = 0 := by
      rw [mul_one, div_self (by linarith), sub_self, hz 0 (by norm_num), zero_div, zero_mul]
    rw [h0, ite_self, zero_add, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (by have := (Finset.mem_Ioc.mp hm).1; omega : 0 < m)
    have e : Real.log ((k * m : ℕ) : ℝ) / Real.log k - 1 = Real.log m / Real.log k := by
      push_cast
      rw [Real.log_mul hκ0.ne' hm0.ne']
      field_simp
      ring
    rw [e]
    field_simp
  rw [hswap, Finset.sum_congr rfl hlevel, ← Finset.sum_sub_distrib]
  have hkbound : ∀ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
      |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0)| ≤
        4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := by
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hk3 : 3 ≤ k := by omega
    have hl := hlogk k hk3
    have hκ0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hrhs : 0 ≤ 4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := by positivity
    have e : ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) =
        -∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          ((if k ∣ n then (k : ℝ) else 0) - 1) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [e, abs_neg]
    by_cases hkb : k ^ 2 ≤ b
    · have hab : a ≤ b ∨ b < a := le_or_gt a b
      rcases hab with hab | hab
      · have hkb' : (k : ℝ) ^ 2 ≤ b := by exact_mod_cast hkb
        have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by positivity) hkb'
        have h1 : 1 ≤ (b : ℝ) * (1 / (k : ℝ) ^ 2) := by
          rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
          exact hkb'
        have h2 : Real.log b ≤ Real.log X := Real.log_le_log hbpos hb
        calc _ ≤ 3 + Real.log b := lattice_level_bound hω hz hk3 ha hab
          _ ≤ 4 * Real.log X * 1 := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
      · rw [Finset.Ioc_eq_empty_of_le hab.le, Finset.sum_empty, abs_zero]
        exact hrhs
    · have hzero : ∑ n ∈ Finset.Ioc a b,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
            ((if k ∣ n then (k : ℝ) else 0) - 1) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hu : Real.log n / Real.log k - 1 < 1 := by
          have h2l : Real.log n < 2 * Real.log k := by
            have := Real.log_lt_log hn0
              (by exact_mod_cast (by omega : n < k ^ 2) : (n : ℝ) < (k : ℝ) ^ 2)
            rw [Real.log_pow] at this
            push_cast at this
            linarith
          have : Real.log n / Real.log k < 2 := (div_lt_iff₀ (by linarith)).mpr h2l
          linarith
        rw [hz _ hu, zero_div, zero_mul]
      rw [hzero, abs_zero]
      exact hrhs
  have hsum : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), 1 / (k : ℝ) ^ 2 ≤ 2 / (z : ℝ) := by
    refine le_trans ?_ (sum_inv_sq_Ico (by omega : 2 ≤ z) (max z (b + 1)) (le_max_left _ _))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hkb : k ≤ b := (Finset.mem_Icc.mp hk1).2
    exact Finset.mem_Ico.mpr ⟨hzk, lt_of_lt_of_le (by omega : k < b + 1) (le_max_right _ _)⟩
  have hzinv : 1 / (z : ℝ) ≤ K * Real.log X ^ (-(A + 1)) := by
    have h1 : 1 / (z : ℝ) ≤ X ^ (-c) := by
      rw [Real.rpow_neg hX0.le, one_div]
      exact inv_anti₀ (Real.rpow_pos_of_pos hX0 c) hzX
    exact h1.trans (hKX X hX3)
  have hpow : Real.log X ^ (-(A + 1)) * Real.log X = Real.log X ^ (-A) := by
    rw [← Real.rpow_add_one hlog0.ne']
    congr 1
    ring
  have hLA : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlog0.le _
  calc _ ≤ ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
          ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
            (if k ∣ n then (k : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := Finset.sum_le_sum hkbound
    _ = 4 * Real.log X * b * ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        1 / (k : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ 4 * Real.log X * b * (2 * (K * Real.log X ^ (-(A + 1)))) := by
        have h2 : 2 / (z : ℝ) = 2 * (1 / (z : ℝ)) := by ring
        have h3 : 2 / (z : ℝ) ≤ 2 * (K * Real.log X ^ (-(A + 1))) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left hzinv (by norm_num)
        exact mul_le_mul_of_nonneg_left (hsum.trans h3) (by positivity)
    _ = 8 * K * b * Real.log X ^ (-A) := by rw [← hpow]; ring
    _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + 8 * K) * b * Real.log X ^ (-A) := by
        have : (0 : ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
        gcongr
        linarith

end LeanLab.BHP1997.LowerShortC165
