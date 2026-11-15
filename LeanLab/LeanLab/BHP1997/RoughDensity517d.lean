/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the rough cofactor of display 5.15 this file holds the step where the prime
number theorem itself is used: in the Buchstab recursion over the least prime factor `p ≥ z`,
the sum over primes `p` of the Buchstab density sums at level `p` is replaced by the sum over
all integers `k ≥ z` with weight `1 / log k`, by `Prime514.pnt_short_interval` and partial
summation in `p` for each cofactor `m`; `prime_weight_transfer` is the result. Nothing is left
open in this file.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prime514
import LeanLab.BHP1997.RoughDensity517c

namespace LeanLab.BHP1997.LowerShortC165
open Classical Decomp132
open scoped BigOperators
open LeanLab.ChenDoubleSieve.Wu04Functional

/-- P0069 page 51, display 5.17, its prime number theorem input at a level: for
`X ^ c ≤ Y ≤ X` the prime count on any `(L, i]` with `i ≤ Y` is the sum of `1 / log k` up to
`Y log^{-A} X`. This is `Prime514.pnt_short_interval` at the ambient scale `Y`. -/
theorem prime_prefix_level {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ X : ℝ, Cq ≤ X → ∀ Y : ℝ, X ^ c ≤ Y → Y ≤ X →
      ∀ L i : ℕ, L ≤ i → (i : ℝ) ≤ Y →
        |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤
          Cq * Y * Real.log X ^ (-A) := by
  obtain ⟨Cp, hCp⟩ := Prime514.pnt_short_interval A hA
  have hT : (0 : ℝ) < max Cp 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcA : 0 < c ^ (-A) := Real.rpow_pos_of_pos hc _
  refine ⟨max ((max Cp 1) ^ (1 / c)) 3 + max Cp 1 * c ^ (-A), by positivity,
    fun X hX Y hXY hYX L i hLi hiY => ?_⟩
  have hX3 : 3 ≤ X := by
    have := le_max_right ((max Cp 1) ^ (1 / c)) 3
    have h2 : 0 < max Cp 1 * c ^ (-A) := by positivity
    linarith
  have hXT : (max Cp 1) ^ (1 / c) ≤ X := by
    have := le_max_left ((max Cp 1) ^ (1 / c)) 3
    have h2 : 0 < max Cp 1 * c ^ (-A) := by positivity
    linarith
  have hX0 : 0 < X := by linarith
  have hTY : max Cp 1 ≤ Y := by
    calc max Cp 1 = ((max Cp 1) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul hT.le, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXT hc.le
      _ ≤ Y := hXY
  have hY1 : 1 ≤ Y := (le_max_right Cp 1).trans hTY
  have hY0 : 0 < Y := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogY : c * Real.log X ≤ Real.log Y := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hXY
    rwa [Real.log_rpow hX0] at h1
  have hcl : 0 < c * Real.log X := by positivity
  have h := hCp Y ((le_max_left Cp 1).trans hTY) (L : ℝ) (i : ℝ) (Nat.cast_nonneg L)
    (by exact_mod_cast hLi) hiY
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  have hpow : Real.log Y ^ (-A) ≤ c ^ (-A) * Real.log X ^ (-A) := by
    rw [← Real.mul_rpow hc.le hlogX.le, Real.rpow_neg (hcl.le.trans hlogY), Real.rpow_neg hcl.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hcl _) (Real.rpow_le_rpow hcl.le hlogY hA.le)
  have hLY : 0 ≤ Real.log Y ^ (-A) := Real.rpow_nonneg (hcl.le.trans hlogY) _
  have hLX : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlogX.le _
  calc _ ≤ Cp * Y * Real.log Y ^ (-A) := h
    _ ≤ max Cp 1 * Y * Real.log Y ^ (-A) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max Cp 1 * Y * (c ^ (-A) * Real.log X ^ (-A)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = max Cp 1 * c ^ (-A) * Y * Real.log X ^ (-A) := by ring
    _ ≤ (max ((max Cp 1) ^ (1 / c)) 3 + max Cp 1 * c ^ (-A)) * Y * Real.log X ^ (-A) := by
        have : (0 : ℝ) ≤ max ((max Cp 1) ^ (1 / c)) 3 := by positivity
        gcongr
        linarith

/-- P0069 page 51, display 5.17, the prime number theorem applied to the least prime factor
`p ≥ z` in the Buchstab recursion, in abstract form. For weights `g m k` that vanish for
`k > m`, are bounded by `1` and vary by at most `E / k` per step in `k`, and prime counts on
intervals below `Y` known up to `R Y`, the sum over primes `p ≥ z` of
`[a < p] + ∑_{a/p < m ≤ b/p, m > 1} g m p` is the sum over all `k ≥ z` of the same weight over
`log k`, up to `R b (1 + (1 + E (1 + log b)) (1 + log b))`. The sums over `m` and the prime are
exchanged and partial summation in the prime is applied for each `m`. -/
theorem prime_transfer_abstract (g : ℕ → ℕ → ℝ) {z a b : ℕ} {E R : ℝ} (hz2 : 2 ≤ z)
    (hzb : z ≤ b) (hE : 0 ≤ E) (hR0 : 0 ≤ R)
    (h0 : ∀ m k : ℕ, 2 ≤ m → m < k → g m k = 0)
    (hstep : ∀ m i : ℕ, z - 1 ≤ i → i + 1 ≤ m → m ≤ b →
      |g m (i + 1) - g m i| ≤ E * ((i : ℝ))⁻¹)
    (hbd : ∀ m k : ℕ, z ≤ k → |g m k| ≤ 1)
    (hR : ∀ Y : ℝ, (z : ℝ) ≤ Y → Y ≤ b → ∀ L i : ℕ, L ≤ i → (i : ℝ) ≤ Y →
      |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤ R * Y) :
    |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
          ((if a < p then (1 : ℝ) else 0) + ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p), g m p) -
        ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          ((if a < k then (1 : ℝ) else 0) + ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), g m k) /
            Real.log k| ≤
      R * b + (1 + E * (1 + Real.log b)) * (R * b * (1 + Real.log b)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
  have hfac : 0 ≤ 1 + E * (1 + Real.log b) :=
    add_nonneg zero_le_one (mul_nonneg hE (by linarith))
  have hRb : 0 ≤ R * b := mul_nonneg hR0 hb0.le
  have hharm : ∑ i ∈ Finset.Icc 1 b, ((i : ℝ))⁻¹ ≤ 1 + Real.log b := by
    have hh : ∑ i ∈ Finset.Icc 1 b, ((i : ℝ))⁻¹ = (harmonic b : ℝ) := by
      simp [harmonic_eq_sum_Icc]
    rw [hh]
    exact harmonic_le_one_add_log b
  have hE1 : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
          ((if a < p then (1 : ℝ) else 0) + ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p), g m p) -
        ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          ((if a < k then (1 : ℝ) else 0) + ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), g m k) /
            Real.log k =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), (primeWeight k - 1 / Real.log (k : ℝ)) *
        ((if a < k then (1 : ℝ) else 0) + ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), g m k) := by
    have hP : (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p) =
        ((Finset.Icc 1 b).filter (fun k => z ≤ k)).filter (fun p => p.Prime) := by
      ext p
      simp only [Finset.mem_filter]
      tauto
    rw [hP, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold primeWeight
    by_cases hp : k.Prime
    · simp only [hp, ite_true]
      ring
    · simp only [hp, ite_false]
      ring
  have hsplit : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        (primeWeight k - 1 / Real.log (k : ℝ)) *
        ((if a < k then (1 : ℝ) else 0) + ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), g m k) =
      ∑ k ∈ Finset.Ioc (max a (z - 1)) b, (primeWeight k - 1 / Real.log (k : ℝ)) +
      ∑ m ∈ Finset.Icc 2 b, ∑ k ∈ Finset.Ioc (max (a / m) (z - 1)) (min (b / m) m),
        g m k * (primeWeight k - 1 / Real.log (k : ℝ)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · have hF : ((Finset.Icc 1 b).filter (fun k => z ≤ k)).filter (fun k => a < k) =
          Finset.Ioc (max a (z - 1)) b := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, max_lt_iff]
        omega
      rw [← hF, Finset.sum_filter (p := fun k => a < k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : a < k <;> simp [h]
    · calc ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            (primeWeight k - 1 / Real.log (k : ℝ)) *
              ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), g m k =
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), ∑ m ∈ Finset.Icc 2 b,
            if a < m * k ∧ m * k ≤ b then
              g m k * (primeWeight k - 1 / Real.log (k : ℝ)) else 0 := by
            refine Finset.sum_congr rfl fun k hk => ?_
            obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
            have hk0 : 0 < k := (Finset.mem_Icc.mp hk1).1
            have hI : Finset.Ioc (max (a / k) 1) (b / k) =
                (Finset.Icc 2 b).filter (fun m => a < m * k ∧ m * k ≤ b) := by
              ext m
              simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc, max_lt_iff,
                Nat.div_lt_iff_lt_mul hk0, Nat.le_div_iff_mul_le hk0]
              have := Nat.le_mul_of_pos_right m hk0
              omega
            rw [hI, Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun m _ => ?_
            by_cases h : a < m * k ∧ m * k ≤ b
            · simp only [h, and_self, ite_true]
              ring
            · simp only [h, ite_false]
        _ = ∑ m ∈ Finset.Icc 2 b, ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            if a < m * k ∧ m * k ≤ b then
              g m k * (primeWeight k - 1 / Real.log (k : ℝ)) else 0 := Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun m hm => ?_
            obtain ⟨hm2, hmb⟩ := Finset.mem_Icc.mp hm
            have hm0 : 0 < m := by omega
            rw [← Finset.sum_filter]
            symm
            refine Finset.sum_subset ?_ ?_
            · intro k hk
              simp only [Finset.mem_Ioc, max_lt_iff, le_min_iff, Nat.div_lt_iff_lt_mul hm0,
                Nat.le_div_iff_mul_le hm0] at hk
              have e : k * m = m * k := mul_comm k m
              have h1 := Nat.le_mul_of_pos_right k hm0
              simp only [Finset.mem_filter, Finset.mem_Icc]
              refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega, by omega⟩
            · intro k hk hnot
              obtain ⟨hkK, hc1, hc2⟩ := Finset.mem_filter.mp hk
              obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hkK
              have hmk : m < k := by
                by_contra hh
                apply hnot
                simp only [Finset.mem_Ioc, max_lt_iff, le_min_iff, Nat.div_lt_iff_lt_mul hm0,
                  Nat.le_div_iff_mul_le hm0]
                have e : k * m = m * k := mul_comm k m
                omega
              rw [h0 m k hm2 hmk, zero_mul]
  have hT1 : |∑ k ∈ Finset.Ioc (max a (z - 1)) b, (primeWeight k - 1 / Real.log (k : ℝ))| ≤
      R * b := by
    by_cases h : max a (z - 1) ≤ b
    · exact hR b (by exact_mod_cast hzb) le_rfl (max a (z - 1)) b h le_rfl
    · rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.sum_empty, abs_zero]
      exact hRb
  have hT2 : ∀ m ∈ Finset.Icc 2 b,
      |∑ k ∈ Finset.Ioc (max (a / m) (z - 1)) (min (b / m) m),
        g m k * (primeWeight k - 1 / Real.log (k : ℝ))| ≤
      (1 + E * (1 + Real.log b)) * (R * b) * ((m : ℝ))⁻¹ := by
    intro m hm
    obtain ⟨hm2, hmb⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    by_cases hLU : max (a / m) (z - 1) < min (b / m) m
    · have hzU : z ≤ min (b / m) m := by omega
      have hUY : ((min (b / m) m : ℕ) : ℝ) ≤ (b : ℝ) / m :=
        le_trans (Nat.cast_le.mpr (min_le_left _ _)) Nat.cast_div_le
      have hzY : (z : ℝ) ≤ (b : ℝ) / m := (Nat.cast_le.mpr hzU).trans hUY
      have hYb : (b : ℝ) / m ≤ b := div_le_self hb0.le (by exact_mod_cast (by omega : 1 ≤ m))
      have hY0 : 0 ≤ (b : ℝ) / m := by positivity
      have habel := abel_Ioc_bound (fun k : ℕ => g m k)
        (fun k : ℕ => primeWeight k - 1 / Real.log (k : ℝ)) hLU.le (R := R * ((b : ℝ) / m))
        (fun i hLi hiU => hR ((b : ℝ) / m) hzY hYb _ i hLi ((Nat.cast_le.mpr hiU).trans hUY))
      have hvar : ∑ i ∈ Finset.Ico (max (a / m) (z - 1)) (min (b / m) m),
          |g m (i + 1) - g m i| ≤ E * (1 + Real.log b) := by
        calc _ ≤ ∑ i ∈ Finset.Ico (max (a / m) (z - 1)) (min (b / m) m), E * ((i : ℝ))⁻¹ :=
              Finset.sum_le_sum (fun i hi => by
                have := Finset.mem_Ico.mp hi
                exact hstep m i (by omega) (by omega) hmb)
          _ = E * ∑ i ∈ Finset.Ico (max (a / m) (z - 1)) (min (b / m) m), ((i : ℝ))⁻¹ :=
              (Finset.mul_sum _ _ _).symm
          _ ≤ E * (1 + Real.log b) := by
              refine mul_le_mul_of_nonneg_left (le_trans ?_ hharm) hE
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
              intro i hi
              have := Finset.mem_Ico.mp hi
              have hdiv := Nat.div_le_self b m
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      calc _ ≤ (|g m (min (b / m) m)| +
            ∑ i ∈ Finset.Ico (max (a / m) (z - 1)) (min (b / m) m), |g m (i + 1) - g m i|) *
              (R * ((b : ℝ) / m)) := habel
        _ ≤ (1 + E * (1 + Real.log b)) * (R * ((b : ℝ) / m)) :=
            mul_le_mul_of_nonneg_right (add_le_add (hbd m _ hzU) hvar) (mul_nonneg hR0 hY0)
        _ = _ := by rw [div_eq_mul_inv]; ring
    · rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.sum_empty, abs_zero]
      exact mul_nonneg (mul_nonneg hfac hRb) (by positivity)
  have hm_sum : ∑ m ∈ Finset.Icc 2 b, ((m : ℝ))⁻¹ ≤ 1 + Real.log b := by
    refine le_trans ?_ hharm
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro i hi
    have := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [hE1, hsplit]
  calc _ ≤ |∑ k ∈ Finset.Ioc (max a (z - 1)) b, (primeWeight k - 1 / Real.log (k : ℝ))| +
        |∑ m ∈ Finset.Icc 2 b, ∑ k ∈ Finset.Ioc (max (a / m) (z - 1)) (min (b / m) m),
          g m k * (primeWeight k - 1 / Real.log (k : ℝ))| := abs_add_le _ _
    _ ≤ R * b + ∑ m ∈ Finset.Icc 2 b, (1 + E * (1 + Real.log b)) * (R * b) * ((m : ℝ))⁻¹ :=
        add_le_add hT1 ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hT2))
    _ = R * b + (1 + E * (1 + Real.log b)) * (R * b) * ∑ m ∈ Finset.Icc 2 b, ((m : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ R * b + (1 + E * (1 + Real.log b)) * (R * b) * (1 + Real.log b) := by
        have := mul_le_mul_of_nonneg_left hm_sum (mul_nonneg hfac hRb)
        linarith
    _ = _ := by ring

/-- P0069 page 51, display 5.17: the Buchstab density `ω(log m / log k) / log k` of a cofactor
`m` varies slowly in the level `k`: one step of the level changes it by at most `(M + 1) / k`
when `log m ≤ M log k`. This is the regularity that partial summation over the prime level
needs. -/
theorem density_level_step {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {M : ℝ} {m i : ℕ} (hi : 3 ≤ i) (him : i + 1 ≤ m) (hM : Real.log m ≤ M * Real.log i) :
    |ω (Real.log m / Real.log ((i + 1 : ℕ) : ℝ)) / Real.log ((i + 1 : ℕ) : ℝ) -
        ω (Real.log m / Real.log i) / Real.log i| ≤ (M + 1) * ((i : ℝ))⁻¹ := by
  have hκ3 : (3 : ℝ) ≤ i := by exact_mod_cast hi
  have hκ0 : (0 : ℝ) < i := by linarith
  have hi1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hl1 : 1 ≤ Real.log i :=
    (Real.le_log_iff_exp_le hκ0).mpr (by linarith [Real.exp_one_lt_d9])
  have hl0 : 0 < Real.log i := by linarith
  have hδ1 : Real.log ((i + 1 : ℕ) : ℝ) - Real.log i ≤ ((i : ℝ))⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (div_pos hi1 hκ0)
    rw [Real.log_div hi1.ne' hκ0.ne'] at h
    have e : ((i + 1 : ℕ) : ℝ) / i - 1 = ((i : ℝ))⁻¹ := by
      push_cast
      field_simp
      ring
    linarith
  have hll : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
    Real.log_le_log hκ0 (by push_cast; linarith)
  have hl'1 : 1 ≤ Real.log ((i + 1 : ℕ) : ℝ) := by linarith
  have hl'0 : 0 < Real.log ((i + 1 : ℕ) : ℝ) := by linarith
  have hl'L : Real.log ((i + 1 : ℕ) : ℝ) ≤ Real.log m :=
    Real.log_le_log hi1 (by exact_mod_cast him)
  have hL0 : 0 < Real.log m := by linarith
  have hM0 : 0 ≤ M := by nlinarith
  have hδ0 : 0 ≤ Real.log ((i + 1 : ℕ) : ℝ) - Real.log i := by linarith
  have hinv0 : (0 : ℝ) ≤ ((i : ℝ))⁻¹ := by positivity
  have hu' : 1 ≤ Real.log m / Real.log ((i + 1 : ℕ) : ℝ) := (one_le_div hl'0).mpr hl'L
  have huu : Real.log m / Real.log ((i + 1 : ℕ) : ℝ) ≤ Real.log m / Real.log i :=
    div_le_div_of_nonneg_left hL0.le hl0 hll
  have hlip := Decomp514a.two_density_buchstab_lipschitz hω hz hu' huu
  have hU : Real.log m / Real.log i - Real.log m / Real.log ((i + 1 : ℕ) : ℝ) ≤
      M * ((i : ℝ))⁻¹ := by
    have e : Real.log m / Real.log i - Real.log m / Real.log ((i + 1 : ℕ) : ℝ) =
        (Real.log m / Real.log i) *
          ((Real.log ((i + 1 : ℕ) : ℝ) - Real.log i) / Real.log ((i + 1 : ℕ) : ℝ)) := by
      field_simp
    rw [e]
    have h1 : Real.log m / Real.log i ≤ M := (div_le_iff₀ hl0).mpr hM
    have h2 : (Real.log ((i + 1 : ℕ) : ℝ) - Real.log i) / Real.log ((i + 1 : ℕ) : ℝ) ≤
        ((i : ℝ))⁻¹ := (div_le_self hδ0 hl'1).trans hδ1
    exact mul_le_mul h1 h2 (div_nonneg hδ0 hl'0.le) hM0
  have e : ω (Real.log m / Real.log ((i + 1 : ℕ) : ℝ)) / Real.log ((i + 1 : ℕ) : ℝ) -
        ω (Real.log m / Real.log i) / Real.log i =
      (ω (Real.log m / Real.log ((i + 1 : ℕ) : ℝ)) - ω (Real.log m / Real.log i)) /
          Real.log ((i + 1 : ℕ) : ℝ) +
        ω (Real.log m / Real.log i) * (1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log i) := by
    field_simp
    ring
  have t1 : |(ω (Real.log m / Real.log ((i + 1 : ℕ) : ℝ)) - ω (Real.log m / Real.log i)) /
      Real.log ((i + 1 : ℕ) : ℝ)| ≤ M * ((i : ℝ))⁻¹ := by
    rw [abs_div, abs_of_pos hl'0]
    exact (div_le_self (abs_nonneg _) hl'1).trans (hlip.trans hU)
  have t2 : |ω (Real.log m / Real.log i) *
      (1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log i)| ≤ ((i : ℝ))⁻¹ := by
    rw [abs_mul]
    have h3 : |1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log i| ≤ ((i : ℝ))⁻¹ := by
      have h4 : 1 / Real.log ((i + 1 : ℕ) : ℝ) ≤ 1 / Real.log i :=
        one_div_le_one_div_of_le hl0 hll
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have h5 : 1 / Real.log i - 1 / Real.log ((i + 1 : ℕ) : ℝ) ≤
          Real.log ((i + 1 : ℕ) : ℝ) - Real.log i := by
        rw [div_sub_div _ _ hl0.ne' hl'0.ne', div_le_iff₀ (by positivity)]
        have hprod : 1 ≤ Real.log i * Real.log ((i + 1 : ℕ) : ℝ) := by nlinarith
        nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hprod)]
      linarith
    calc _ ≤ 1 * ((i : ℝ))⁻¹ :=
          mul_le_mul (abs_buchstab_le_one hω hz _) h3 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ M * ((i : ℝ))⁻¹ + ((i : ℝ))⁻¹ := add_le_add t1 t2
    _ = _ := by ring

/-- P0069 page 51, display 5.17, the prime number theorem applied to the least prime factor in
the Buchstab recursion for densities: the sum over primes `p ≥ z` of
`[a < p] + ∑_{a/p < m ≤ b/p, m > 1} ω(log m / log p) / log p` is the sum over all integers
`k ≥ z` of the same weight divided by `log k`, with every log power saved. -/
theorem prime_weight_transfer (ω : ℝ → ℝ) (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            ((if a < k then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
                ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.log X ^ (-A) := by
  obtain ⟨Cq, hCq, hpnt⟩ := prime_prefix_level hc (A + 2) (by linarith)
  have hE : (0 : ℝ) ≤ 2 / c + 1 := by positivity
  refine ⟨max ((4 : ℝ) ^ (1 / c)) 4 + Cq + (3 + 4 * (2 / c + 1)) * Cq, by positivity,
    fun X hX z hzX a b ha hb => ?_⟩
  have hpos2 : 0 < (3 + 4 * (2 / c + 1)) * Cq := by positivity
  have hX4 : 4 ≤ X := by linarith [le_max_right ((4 : ℝ) ^ (1 / c)) 4]
  have hXc : (4 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((4 : ℝ) ^ (1 / c)) 4]
  have hXq : Cq ≤ X := by
    have : (0 : ℝ) ≤ max ((4 : ℝ) ^ (1 / c)) 4 := by positivity
    linarith
  have hX0 : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 < Real.log X := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hLA : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlog0.le _
  have hr0 : 0 ≤ Real.log X ^ (-(A + 2)) := Real.rpow_nonneg hlog0.le _
  have h4z : (4 : ℝ) ≤ z := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  have hz4 : 4 ≤ z := by exact_mod_cast h4z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogk : ∀ k : ℕ, 3 ≤ k → 1 ≤ Real.log k := by
    intro k hk
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  by_cases hzb : z ≤ b
  swap
  · have hK : (Finset.Icc 1 b).filter (fun k => z ≤ k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    have hP : (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    rw [hK, hP, Finset.sum_empty, Finset.sum_empty, sub_zero, abs_zero]
    positivity
  have hmain := prime_transfer_abstract
    (fun m k : ℕ => ω (Real.log m / Real.log k) / Real.log k) (a := a)
    (E := 2 / c + 1) (R := Cq * Real.log X ^ (-(A + 2))) (by omega : 2 ≤ z) hzb hE
    (by positivity)
    (by
      intro m k hm hmk
      have hl := hlogk k (by omega)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hu : Real.log m / Real.log k < 1 := by
        rw [div_lt_one (by linarith)]
        exact Real.log_lt_log hm0 (by exact_mod_cast hmk)
      rw [hz _ hu, zero_div])
    (by
      intro m i hzi him hmb
      have hi3 : 3 ≤ i := by omega
      have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hi2 : i + 1 ≤ i ^ 2 := by nlinarith
      have hzi2 : z ≤ i ^ 2 := le_trans (by omega) hi2
      have h1 : Real.log z ≤ 2 * Real.log i := by
        have := Real.log_le_log hz0 (by exact_mod_cast hzi2 : (z : ℝ) ≤ (i : ℝ) ^ 2)
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have h2 : Real.log m ≤ Real.log X :=
        Real.log_le_log hm0 (le_trans (by exact_mod_cast hmb) hb)
      have h3 : 1 / c * Real.log z ≤ 1 / c * (2 * Real.log i) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have hM : Real.log m ≤ 2 / c * Real.log i := by
        have e : 1 / c * (2 * Real.log i) = 2 / c * Real.log i := by ring
        linarith
      exact density_level_step hω hz hi3 him hM)
    (by
      intro m k hzk
      have hl := hlogk k (by omega)
      rw [abs_div, abs_of_pos (by linarith : 0 < Real.log k)]
      exact (div_le_one (by linarith)).mpr ((abs_buchstab_le_one hω hz _).trans hl))
    (by
      intro Y hzY hYb L i hLi hiY
      exact le_of_le_of_eq (hpnt X hXq Y (hzX.trans hzY) (hYb.trans hb) L i hLi hiY) (by ring))
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
  have hlb : Real.log b ≤ Real.log X := Real.log_le_log hbpos hb
  have hpow2 : Real.log X ^ (-(A + 2)) * Real.log X ^ 2 = Real.log X ^ (-A) := by
    rw [← Real.rpow_two, ← Real.rpow_add hlog0]
    congr 1
    ring
  have h1 : 1 + Real.log b ≤ 2 * Real.log X := by linarith
  have h2 : 1 + (2 / c + 1) * (1 + Real.log b) ≤ (1 + 2 * (2 / c + 1)) * Real.log X := by
    nlinarith
  have h3 : (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b) ≤
      ((1 + 2 * (2 / c + 1)) * Real.log X) * (2 * Real.log X) :=
    mul_le_mul h2 h1 (by linarith) (by positivity)
  have h4 : 1 ≤ Real.log X ^ 2 := by nlinarith
  have hCb : 0 ≤ Cq * Real.log X ^ (-(A + 2)) * b := by positivity
  calc _ ≤ Cq * Real.log X ^ (-(A + 2)) * b + (1 + (2 / c + 1) * (1 + Real.log b)) *
        (Cq * Real.log X ^ (-(A + 2)) * b * (1 + Real.log b)) := hmain
    _ = Cq * Real.log X ^ (-(A + 2)) * b *
        (1 + (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b)) := by ring
    _ ≤ Cq * Real.log X ^ (-(A + 2)) * b *
        ((3 + 4 * (2 / c + 1)) * Real.log X ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hCb
        nlinarith
    _ = (3 + 4 * (2 / c + 1)) * Cq * b * Real.log X ^ (-A) := by rw [← hpow2]; ring
    _ ≤ _ := by
        have : (0 : ℝ) ≤ max ((4 : ℝ) ^ (1 / c)) 4 := by positivity
        gcongr
        linarith

end LeanLab.BHP1997.LowerShortC165
