/-
Relative prime reciprocal bands for the dimension two input.
Source: Kumchev and Liu page 13 display 44 and page 17 before display 58.
The estimate is a derived partial summation step from the lab Mertens bounds.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTSieve.MertensLower
import LeanLab.PNTSieve.MertensProduct

namespace LeanLab.KumchevLiu2007.Task558c
open LeanLab.PNTSieve.Mertens
open Finset Real
open scoped BigOperators

/-- Page 13 display 44, the logarithmic kernel in discrete partial summation. -/
theorem log_kernel_step (k : ℕ) (hk : 2 ≤ k) :
    Real.log k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) ≤
      Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hl : 0 < Real.log k := Real.log_pos (by linarith)
  have hl1 : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  rw [← Real.log_div hl1.ne' hl.ne']
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hl1 hl)
  rw [inv_div] at h
  have he : Real.log k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) =
      1 - Real.log k / Real.log ((k : ℝ) + 1) := by field_simp
  rwa [he]

/-- Page 13 display 44, exact partial summation on an integer band. -/
theorem reciprocal_band_abel (M N : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) :
    E N - E M = C N / Real.log N - C M / Real.log M +
      ∑ k ∈ Ico M N, C k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) := by
  have hs := sum_Ico_consecutive (fun k : ℕ => C k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1))) hM hMN
  rw [abel N (hM.trans hMN), abel M hM, ← hs]
  ring

/-- Page 13 display 44 and page 17 dimension two estimate, reciprocal primes
on an integer band have the correct log log difference and a relative error. -/
theorem reciprocal_band_bound (M N : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) :
    E N - E M ≤ Real.log (Real.log N) - Real.log (Real.log M) + 14 / Real.log M := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hM.trans hMN
  have hLM : 0 < Real.log M := Real.log_pos (by linarith)
  have hLN : 0 < Real.log N := Real.log_pos (by linarith)
  have hCN : C N / Real.log N ≤ 1 + 7 / Real.log N := by
    rw [div_le_iff₀ hLN, add_mul, one_mul, div_mul_cancel₀ _ hLN.ne']
    linarith [C_le N (by omega)]
  have hCM : 1 - 7 / Real.log M ≤ C M / Real.log M := by
    rw [le_div_iff₀ hLM, sub_mul, one_mul, div_mul_cancel₀ _ hLM.ne']
    linarith [C_ge M]
  have hterm : ∀ k ∈ Ico M N,
      C k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) ≤
        Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) +
          7 * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) := by
    intro k hk
    have hk2 := hM.trans (mem_Ico.mp hk).1
    have hc := mul_le_mul_of_nonneg_right (C_le k (by omega)) (diff_nonneg hk2)
    nlinarith [log_kernel_step k hk2]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hsum
  have ht (f : ℕ → ℝ) : ∑ k ∈ Ico M N, (f (k + 1) - f k) = f N - f M := by
    exact sum_Ico_sub f hMN
  have ht1 : (∑ k ∈ Ico M N, (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k))) =
      Real.log (Real.log N) - Real.log (Real.log M) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht (fun k => Real.log (Real.log k))
  have ht2 : (∑ k ∈ Ico M N, (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1))) =
      1 / Real.log M - 1 / Real.log N := by
    have hh := ht (fun k => -(1 / Real.log k))
    push_cast at hh
    simpa only [neg_sub_neg] using hh
  rw [ht1, ht2] at hsum
  rw [reciprocal_band_abel M N hM hMN]
  simp only [div_eq_mul_inv, one_mul] at *
  linarith

/-- Page 13 display 44, the reciprocal prime band in real cutoff notation. -/
noncomputable def primeReciprocalBand (w v : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊v⌋₊ + 1)).filter
      (fun (p : ℕ) => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < v), (1 : ℝ) / p

/-- Page 13 display 44, the band sum is the difference of the discrete
partial sums. -/
theorem prime_reciprocal_Ioc (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
    (∑ p ∈ (Ioc M N).filter Nat.Prime, (1 : ℝ) / p) = E N - E M := by
  have hi : Icc 1 N = Icc 1 M ∪ Ioc M N := by
    ext k
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 M) (Ioc M N) := by
    apply disjoint_left.mpr
    intro k hk hkk
    exact (not_lt_of_ge (mem_Icc.mp hk).2) (mem_Ioc.mp hkk).1
  have hs : E N = E M + ∑ p ∈ Ioc M N, c p / Real.log p := by
    unfold E
    rw [hi, sum_union hd]
  have ht : (∑ p ∈ Ioc M N, c p / Real.log p) =
      ∑ p ∈ (Ioc M N).filter Nat.Prime, (1 : ℝ) / p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    unfold c
    split_ifs with hprime
    · have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hprime.one_lt)
      field_simp
    · simp
  rw [ht] at hs
  linarith

/-- Page 13 display 44, a real band lies inside its integer band together
with the possible lower endpoint prime. -/
theorem primeReciprocalBand_le_floor (w v : ℝ) (hw : 2 ≤ w) (hwv : w ≤ v) :
    primeReciprocalBand w v ≤ E ⌊v⌋₊ - E ⌊w⌋₊ + 1 / (⌊w⌋₊ : ℝ) := by
  classical
  have hM : 2 ≤ ⌊w⌋₊ := Nat.le_floor hw
  have hMN : ⌊w⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono hwv
  let S := (range (⌊v⌋₊ + 1)).filter
      (fun (p : ℕ) => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < v)
  let T := (Ioc ⌊w⌋₊ ⌊v⌋₊).filter Nat.Prime
  have hsub : S ⊆ insert ⌊w⌋₊ T := by
    intro p hp
    obtain ⟨hpr, hpw, hpv⟩ := (mem_filter.mp hp).2
    have hMle : ⌊w⌋₊ ≤ p := by exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ w)).trans hpw
    have hpN : p ≤ ⌊v⌋₊ := Nat.le_floor hpv.le
    by_cases he : p = ⌊w⌋₊
    · simp [he]
    · apply mem_insert_of_mem
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpN⟩, hpr⟩
  have hsum : (∑ p ∈ S, (1 : ℝ) / p) ≤ ∑ p ∈ insert ⌊w⌋₊ T, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hmnot : ⌊w⌋₊ ∉ T := by simp [T]
  rw [sum_insert hmnot, prime_reciprocal_Ioc ⌊w⌋₊ ⌊v⌋₊ (by omega) hMN] at hsum
  dsimp [S] at hsum
  simpa only [primeReciprocalBand, add_comm] using hsum

/-- Page 13 display 44, replacing a real lower cutoff by its floor costs
at most two inverse logarithms in the log log boundary term and endpoint. -/
theorem floor_log_comparison (w : ℝ) (hw : 2 ≤ w) :
    Real.log (Real.log w) - Real.log (Real.log (⌊w⌋₊ : ℝ)) ≤ 2 / Real.log w ∧
      1 / (⌊w⌋₊ : ℝ) ≤ 2 / Real.log w ∧
      1 / Real.log (⌊w⌋₊ : ℝ) ≤ 2 / Real.log w := by
  let M := ⌊w⌋₊
  have hM : 2 ≤ M := Nat.le_floor hw
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hLM : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hLw : 0 < Real.log w := Real.log_pos (by linarith)
  have hMw : (M : ℝ) ≤ w := Nat.floor_le (by linarith)
  have hwM : w ≤ 2 * (M : ℝ) := by
    have h := Nat.lt_floor_add_one w
    dsimp [M] at *
    linarith
  have hLadd : Real.log w ≤ Real.log 2 + Real.log (M : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hwM
  have hLtwo : Real.log 2 ≤ Real.log (M : ℝ) := Real.log_le_log (by norm_num) hMR
  have hLratio : Real.log w ≤ 2 * Real.log (M : ℝ) := by linarith
  have hinv : 1 / Real.log (M : ℝ) ≤ 2 / Real.log w := by
    rw [div_le_div_iff₀ hLM hLw]
    linarith
  refine ⟨?_, ?_, hinv⟩
  · have hlog : Real.log (Real.log w) - Real.log (Real.log (M : ℝ)) ≤
        (Real.log w - Real.log (M : ℝ)) / Real.log (M : ℝ) := by
      rw [← Real.log_div hLw.ne' hLM.ne']
      have h := Real.log_le_sub_one_of_pos (div_pos hLw hLM)
      convert h using 1 <;> field_simp
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hdelta : Real.log w - Real.log (M : ℝ) ≤ 1 := by linarith
    exact hlog.trans ((div_le_div_of_nonneg_right hdelta hLM.le).trans hinv)
  · have hlogM : Real.log (M : ℝ) ≤ (M : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < M)]
    exact (one_div_le_one_div_of_le hLM hlogM).trans hinv

/-- Page 13 display 44 and page 17 dimension two estimate, prime reciprocals
on a real band have the log log ratio plus a uniform inverse log error. -/
theorem primeReciprocalBand_bound (w v : ℝ) (hw : 2 ≤ w) (hwv : w < v) :
    primeReciprocalBand w v ≤ Real.log (Real.log v) - Real.log (Real.log w) +
      32 / Real.log w := by
  have hM : 2 ≤ ⌊w⌋₊ := Nat.le_floor hw
  have hN : 2 ≤ ⌊v⌋₊ := Nat.le_floor (hw.trans hwv.le)
  have hMN : ⌊w⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono hwv.le
  have hNR : (2 : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast hN
  have hlogN : 0 < Real.log (⌊v⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlog_le : Real.log (Real.log (⌊v⌋₊ : ℝ)) ≤ Real.log (Real.log v) :=
    Real.log_le_log hlogN (Real.log_le_log (by linarith)
      (Nat.floor_le (by linarith : 0 ≤ v)))
  obtain ⟨hfloor, hendpoint, hinv⟩ := floor_log_comparison w hw
  have hb := reciprocal_band_bound ⌊w⌋₊ ⌊v⌋₊ hM hMN
  have hreal := primeReciprocalBand_le_floor w v hw hwv.le
  simp only [div_eq_mul_inv, one_mul] at *
  linarith


/-- Page 17 dimension two comparison, the reciprocal square tail on a
real prime band is bounded by four inverse logarithms of its lower cutoff. -/
theorem prime_square_band_bound (w v : ℝ) (hw : 2 ≤ w) (hwv : w < v) :
    (∑ p ∈ (range (⌊v⌋₊ + 1)).filter
      (fun (p : ℕ) => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < v),
        ((p : ℝ) ^ 2)⁻¹) ≤ 4 / Real.log w := by
  classical
  let M := ⌊w⌋₊
  let N := ⌊v⌋₊
  let S := (range (N + 1)).filter
      (fun (p : ℕ) => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < v)
  have hM : 2 ≤ M := Nat.le_floor hw
  have hMN : M ≤ N := Nat.floor_mono hwv.le
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hsub : S ⊆ insert M (Ioc M N) := by
    intro p hp
    obtain ⟨hpr, hpw, hpv⟩ := (mem_filter.mp hp).2
    have hMle : M ≤ p := by exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ w)).trans hpw
    have hpN : p ≤ N := Nat.le_floor hpv.le
    by_cases he : p = M
    · simp [he]
    · exact mem_insert_of_mem (mem_Ioc.mpr ⟨by omega, hpN⟩)
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => ((p : ℝ) ^ 2)⁻¹)
    hsub (fun _ _ _ => by positivity)
  rw [sum_insert (by simp)] at hsum
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := M) (n := N) (by omega) hMN
  have hsq : ((M : ℝ) ^ 2)⁻¹ ≤ (M : ℝ)⁻¹ := by
    apply inv_anti₀ (by linarith)
    nlinarith
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hfloor := (floor_log_comparison w hw).2.1
  change 1 / (M : ℝ) ≤ 2 / Real.log w at hfloor
  change (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ 4 / Real.log w
  simp only [div_eq_mul_inv] at *
  linarith

/-- Page 17 dimension two comparison, the maximal local factor has a
prime reciprocal main term and a summable reciprocal square error. -/
theorem log_majorant_factor (p : ℕ) (hp : 5 ≤ p) :
    Real.log ((1 - 2 / ((p : ℝ) - 1))⁻¹) ≤ 2 / (p : ℝ) + 16 / (p : ℝ) ^ 2 := by
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hpp : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hg0 : 0 ≤ 2 / ((p : ℝ) - 1) := by positivity
  have hg1 : 2 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ hp1]
    linarith
  have hlog := log_one_sub_ge (2 / ((p : ℝ) - 1)) hg0 hg1
  rw [Real.log_inv]
  have harith : 2 / ((p : ℝ) - 1) + 2 * (2 / ((p : ℝ) - 1)) ^ 2 ≤
      2 / (p : ℝ) + 16 / (p : ℝ) ^ 2 := by
    field_simp
    nlinarith [sq_nonneg ((p : ℝ) - 5)]
  linarith

/-- Page 13 display 44, exponentiating an inverse log error gives a
fixed constant times the same inverse log error. -/
theorem exp_inverse_log_bound (A w : ℝ) (hA : 0 ≤ A) (hw : 2 ≤ w) :
    Real.exp (A / Real.log w) ≤ 1 + (A * Real.exp (A / Real.log 2)) / Real.log w := by
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLw : 0 < Real.log w := Real.log_pos (by linarith)
  have ht : 0 ≤ A / Real.log w := div_nonneg hA hLw.le
  have hL : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have he : Real.exp (A / Real.log w) ≤ Real.exp (A / Real.log 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hA hL2 hL)
  have hbase := Real.add_one_le_exp (-(A / Real.log w))
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (A / Real.log w)).le
  have hcancel : Real.exp (A / Real.log w) * Real.exp (-(A / Real.log w)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at hmul
  have hreplace := mul_le_mul_of_nonneg_left he ht
  have hid : (A / Real.log w) * Real.exp (A / Real.log 2) =
      (A * Real.exp (A / Real.log 2)) / Real.log w := by ring
  rw [hid] at hreplace
  nlinarith

end LeanLab.KumchevLiu2007.Task558c
