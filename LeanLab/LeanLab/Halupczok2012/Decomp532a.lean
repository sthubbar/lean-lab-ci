import LeanLab.Halupczok2012.U1439Combin
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
Halupczok journal pages 336 to 337, Lemma 2.1 and display 2.2.
The divisor factorization precedes the short interval Voronoi input.
https://doi.org/10.5802/jtnb.839
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp532a

open Finset
open scoped Classical Pointwise

/-- Divisor submultiplicativity in page 337 display 2.2. -/
theorem divisor_count_mul_le (u v : ℕ) :
    ((u * v).divisors.card : ℝ) ≤ (u.divisors.card : ℝ) * v.divisors.card := by
  exact_mod_cast (show (u * v).divisors.card ≤ u.divisors.card * v.divisors.card by
    rw [Nat.divisors_mul]
    exact Finset.card_mul_le)

/-- The first exchange of overlap sums in page 337 display 2.2. -/
theorem overlap_sum (W U : Finset ℕ) :
    ∑ s ∈ W, (((U.filter (fun u => u ∣ s)).card : ℝ) ^ 2) =
      ∑ u ∈ U, ∑ v ∈ U, (((W.filter (fun s => u ∣ s ∧ v ∣ s)).card : ℝ)) := by
  have hs (s : ℕ) : ((U.filter (fun u => u ∣ s)).card : ℝ) ^ 2 =
      ∑ u ∈ U, ∑ v ∈ U, (if u ∣ s ∧ v ∣ s then (1 : ℝ) else 0) := by
    rw [card_filter, sq]
    push_cast
    rw [sum_mul_sum]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    by_cases hu : u ∣ s <;> by_cases hv : v ∣ s <;> simp [hu, hv]
  simp_rw [hs]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [card_filter]
  push_cast
  rfl

/-- The factor exchange in page 337 display 2.2. -/
theorem divisor_factor_exchange (W U : Finset ℕ) :
    ∑ s ∈ W, ((U.filter (fun u => u ∣ s)).card : ℝ) ^ 2 =
      ∑ u ∈ U, ∑ s ∈ W.filter (fun s => u ∣ s),
        ((U.filter (fun v => v ∣ s)).card : ℝ) := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  rw [sq, card_filter]
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp

/-- A truncated divisor count is at most the full count for a positive integer.
This is the inequality in page 337 display 2.2. -/
theorem truncated_count_le (U : Finset ℕ) {s : ℕ} (hs : 0 < s) :
    ((U.filter (fun u => u ∣ s)).card : ℝ) ≤ (s.divisors.card : ℝ) := by
  exact_mod_cast card_le_card (show U.filter (fun u => u ∣ s) ⊆ s.divisors by
    intro u hu
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hu).2, by omega⟩)

/-- Reindex the factor u by the complementary divisor v on page 337 display 2.2. -/
theorem complementary_divisor_sum (W : Finset ℕ) (B u : ℕ) (hu : 0 < u)
    (hW : ∀ s ∈ W, 0 < s ∧ s ≤ B) :
    ∑ s ∈ W.filter (fun s => u ∣ s), (s.divisors.card : ℝ) =
      ∑ v ∈ (Icc 1 B).filter (fun v => u * v ∈ W), ((u * v).divisors.card : ℝ) := by
  symm
  apply sum_bij (fun v _ => u * v)
  · intro v hv
    exact mem_filter.mpr ⟨(mem_filter.mp hv).2, dvd_mul_right u v⟩
  · intro v _ w _ he
    exact Nat.eq_of_mul_eq_mul_left hu he
  · intro s hs
    obtain ⟨hsW, hdu⟩ := mem_filter.mp hs
    obtain ⟨hs0, hsB⟩ := hW s hsW
    have he : u * (s / u) = s := Nat.mul_div_cancel' hdu
    refine ⟨s / u, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩, he⟩
    · have hpos : 0 < s / u := by
        apply Nat.div_pos
        · exact Nat.le_of_dvd hs0 hdu
        · exact hu
      exact hpos
    · exact (Nat.div_le_self s u).trans hsB
    · simpa [he] using hsW
  · intro v _
    rfl

/-- The complete elementary factorization bound of page 337 display 2.2. -/
theorem overlap_factor_bound (W U : Finset ℕ) (B : ℕ)
    (hW : ∀ s ∈ W, 0 < s ∧ s ≤ B) (hU : ∀ u ∈ U, 0 < u) :
    ∑ s ∈ W, ((U.filter (fun u => u ∣ s)).card : ℝ) ^ 2 ≤
      ∑ u ∈ U, (u.divisors.card : ℝ) *
        ∑ v ∈ (Icc 1 B).filter (fun v => u * v ∈ W), (v.divisors.card : ℝ) := by
  rw [divisor_factor_exchange]
  apply sum_le_sum
  intro u hu
  calc
    _ ≤ ∑ s ∈ W.filter (fun s => u ∣ s), (s.divisors.card : ℝ) := by
      apply sum_le_sum
      intro s hs
      exact truncated_count_le U (hW s (mem_filter.mp hs).1).1
    _ = ∑ v ∈ (Icc 1 B).filter (fun v => u * v ∈ W), ((u * v).divisors.card : ℝ) :=
      complementary_divisor_sum W B u (hU u hu) hW
    _ ≤ ∑ v ∈ (Icc 1 B).filter (fun v => u * v ∈ W),
        (u.divisors.card : ℝ) * v.divisors.card :=
      sum_le_sum fun v _ => divisor_count_mul_le u v
    _ = _ := (mul_sum _ _ _).symm

/-- The reciprocal divisor sum used after page 337 display 2.2. -/
theorem divisor_reciprocal_sum (N : ℕ) :
    ∑ u ∈ Icc 1 N, (u.divisors.card : ℝ) / u ≤ (1 + Real.log N) ^ 2 := by
  have he (u : ℕ) (hu : u ∈ Icc 1 N) :
      (u.divisors.card : ℝ) / u =
        ∑ d ∈ Icc 1 N, (if d ∣ u then (u : ℝ)⁻¹ else 0) := by
    have hu0 : u ≠ 0 := by have := (mem_Icc.mp hu).1; omega
    have hd : u.divisors = (Icc 1 N).filter (fun d => d ∣ u) := by
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hdu, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdu (Nat.pos_of_ne_zero hu0),
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hu0) hdu).trans (mem_Icc.mp hu).2⟩, hdu⟩
      · rintro ⟨_, hdu⟩
        exact ⟨hdu, hu0⟩
    rw [hd, div_eq_mul_inv, card_filter]
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp
  calc
    _ = ∑ u ∈ Icc 1 N, ∑ d ∈ Icc 1 N, (if d ∣ u then (u : ℝ)⁻¹ else 0) :=
      sum_congr rfl he
    _ = ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, (if d ∣ u then (u : ℝ)⁻¹ else 0) := sum_comm
    _ ≤ ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ * (1 + Real.log N) := by
      apply sum_le_sum
      intro d hd
      exact sum_dvd_inv_le N d (mem_Icc.mp hd).1
    _ = (∑ d ∈ Icc 1 N, (d : ℝ)⁻¹) * (1 + Real.log N) := (sum_mul _ _ _).symm
    _ ≤ (1 + Real.log N) ^ 2 := by
      simpa [sq] using mul_le_mul_of_nonneg_right (sum_inv_Icc_le N) (one_add_log_nonneg N)

/-- The weighted reciprocal sum after page 337 display 2.2.
The factor u to the two thirds is at most N to the two thirds. -/
theorem divisor_third_sum (N : ℕ) :
    ∑ u ∈ Icc 1 N, (u.divisors.card : ℝ) * (u : ℝ) ^ (-(1 / 3) : ℝ) ≤
      (N : ℝ) ^ (2 / 3 : ℝ) * (1 + Real.log N) ^ 2 := by
  calc
    _ = ∑ u ∈ Icc 1 N, ((u.divisors.card : ℝ) / u) * (u : ℝ) ^ (2 / 3 : ℝ) := by
      apply sum_congr rfl
      intro u hu
      have hu0 : (0 : ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
      rw [show (-(1 / 3) : ℝ) = 2 / 3 - 1 by norm_num,
        Real.rpow_sub hu0, Real.rpow_one]
      ring
    _ ≤ ∑ u ∈ Icc 1 N, ((u.divisors.card : ℝ) / u) * (N : ℝ) ^ (2 / 3 : ℝ) := by
      apply sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (mem_Icc.mp hu).2)
        (by norm_num)
    _ = (N : ℝ) ^ (2 / 3 : ℝ) * ∑ u ∈ Icc 1 N, (u.divisors.card : ℝ) / u := by
      rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisor_reciprocal_sum N) (by positivity)

/-- LEAF. Halupczok journal page 337, the printed Voronoi formula below display 2.2.
The error is O of x to one third times log x as x tends to infinity.
The threshold is at least two and the implied constant is positive. -/
theorem voronoi_divisor_sum_asymptotic :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
          C * x ^ (1 / 3 : ℝ) * Real.log x := by
  sorry

/-- Extend the eventual Voronoi bound across the bounded initial range on page 337.
This implication is CONDITIONAL ON the explicit eventual summatory estimate. -/
theorem divisor_sum_global_of_eventual (C b X0 : ℝ) (hC : 0 ≤ C)
    (hV : ∀ x : ℝ, X0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) - (x * Real.log x + b * x)| ≤
        C * x ^ (1 / 3 : ℝ) * Real.log x) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) - (x * Real.log x + b * x)| ≤
        D * x ^ (1 / 3 : ℝ) * (1 + Real.log x) := by
  let T := max X0 2
  let S := ∑ n ∈ Icc 1 ⌊T⌋₊, (n.divisors.card : ℝ)
  let D := C + S + T * Real.log T + |b| * T + 1
  have hT2 : 2 ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hS : 0 ≤ S := sum_nonneg fun _ _ => by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hDC : C ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg hT0.le hlogT, mul_nonneg (abs_nonneg b) hT0.le]
  refine ⟨D, hD, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp : 0 ≤ x ^ (1 / 3 : ℝ) := by positivity
  by_cases hxT : T ≤ x
  · calc
      _ ≤ C * x ^ (1 / 3 : ℝ) * Real.log x := hV x ((le_max_left _ _).trans hxT)
      _ ≤ D * x ^ (1 / 3 : ℝ) * (1 + Real.log x) := by gcongr; linarith
  · have hxT' : x ≤ T := le_of_lt (lt_of_not_ge hxT)
    have hsum : (∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) ≤ S := by
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.floor_mono hxT'))
        (fun _ _ _ => by positivity)
    have hsum0 : 0 ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) := sum_nonneg fun _ _ => by positivity
    have hl : Real.log x ≤ Real.log T := Real.log_le_log hx0 hxT'
    have hxl : x * Real.log x ≤ T * Real.log T := mul_le_mul hxT' hl hlogx hT0.le
    have hbx : |b| * x ≤ |b| * T := mul_le_mul_of_nonneg_left hxT' (abs_nonneg b)
    have hsmall : |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
        (x * Real.log x + b * x)| ≤ S + T * Real.log T + |b| * T := by
      have hbU := mul_le_mul_of_nonneg_right (le_abs_self b) hx0.le
      have hbL := mul_le_mul_of_nonneg_right (neg_abs_le b) hx0.le
      apply abs_le.mpr
      constructor <;> nlinarith [mul_nonneg hx0.le hlogx, mul_nonneg hT0.le hlogT]
    have hxpow : 1 ≤ x ^ (1 / 3 : ℝ) := Real.one_le_rpow hx (by norm_num)
    have hden : 1 ≤ x ^ (1 / 3 : ℝ) * (1 + Real.log x) := by nlinarith [mul_nonneg (sub_nonneg.mpr hxpow) hlogx]
    calc
      _ ≤ S + T * Real.log T + |b| * T := hsmall
      _ ≤ D := by dsimp [D]; linarith
      _ ≤ D * (x ^ (1 / 3 : ℝ) * (1 + Real.log x)) := le_mul_of_one_le_right hD.le hden
      _ = _ := by ring
/-- Halupczok journal page 337, the Voronoi formula below display 2.2.
The divisor summatory error has exponent one third and one logarithmic factor.
The factor 1 plus log x extends the estimate to every x at least one by enlarging C. -/
theorem voronoi_divisor_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
          C * x ^ (1 / 3 : ℝ) * (1 + Real.log x) := by
  obtain ⟨C, X0, hC, _hX0, hV⟩ := voronoi_divisor_sum_asymptotic
  exact divisor_sum_global_of_eventual C (2 * Real.eulerMascheroniConstant - 1) X0 hC.le hV

/-- The elementary main term difference under the Voronoi formula on page 337. -/
theorem divisor_main_increment (b x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    (y * Real.log y + b * y) - (x * Real.log x + b * x) ≤
      (y - x) * (1 + |b| + Real.log y) := by
  have hy : 0 < y := hx.trans_le hxy
  have hh := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hh
  have hhx := mul_le_mul_of_nonneg_left hh hx.le
  have he : x * (y / x - 1) = y - x := by field_simp
  rw [he] at hhx
  have hb := mul_le_mul_of_nonneg_right (le_abs_self b) (sub_nonneg.mpr hxy)
  nlinarith

/-- Subtract the two natural cutoff sums in page 337 display 2.2. -/
theorem divisor_window_difference (x y : ℝ) (hxy : x ≤ y) :
    ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (n.divisors.card : ℝ) =
      (∑ n ∈ Icc 1 ⌊y⌋₊, (n.divisors.card : ℝ)) -
        ∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) := by
  have hsub : Icc 1 ⌊x⌋₊ ⊆ Icc 1 ⌊y⌋₊ := Icc_subset_Icc_right (Nat.floor_mono hxy)
  have he : Icc 1 ⌊y⌋₊ \ Icc 1 ⌊x⌋₊ = Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n
    simp only [mem_sdiff, mem_Icc, mem_Ioc]
    omega
  rw [← he]
  exact eq_sub_iff_add_eq.mpr (sum_sdiff hsub)
/-- The large endpoint case of differencing Voronoi on page 337. -/
theorem large_divisor_interval_of_summatory (C b M x y : ℝ)
    (hC : 0 ≤ C) (hM : 2 ≤ M) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hxM : x ≤ M) (hyx : y ≤ 3 * x)
    (hxV : |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
      (x * Real.log x + b * x)| ≤ C * x ^ (1 / 3 : ℝ) * (1 + Real.log x))
    (hyV : |(∑ n ∈ Icc 1 ⌊y⌋₊, (n.divisors.card : ℝ)) -
      (y * Real.log y + b * y)| ≤ C * y ^ (1 / 3 : ℝ) * (1 + Real.log y)) :
    ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (n.divisors.card : ℝ) ≤
      (1 + |b| + Real.log 3 + 4 * C * (1 + Real.log 3)) *
        ((y - x) + x ^ (1 / 3 : ℝ)) * (1 + Real.log M) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hM0 : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogx : Real.log x ≤ Real.log M := Real.log_le_log hx0 hxM
  have hlogy : Real.log y ≤ Real.log 3 + Real.log M := by
    have hh := Real.log_le_log hy0 (show y ≤ 3 * M by linarith)
    rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hM0.ne'] at hh
  have hlogx0 : 0 ≤ 1 + Real.log x := by
    have := Real.log_nonneg hx
    linarith
  have hlogy0 : 0 ≤ 1 + Real.log y := by
    have := Real.log_nonneg (hx.trans hxy)
    linarith
  have hyPow : y ^ (1 / 3 : ℝ) ≤ 3 * x ^ (1 / 3 : ℝ) := by
    calc
      _ ≤ (3 * x) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow hy0.le hyx (by norm_num)
      _ = (3 : ℝ) ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 3 * x ^ (1 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (by norm_num : (1 / 3 : ℝ) ≤ 1) using 1 <;> norm_num
  have hxLog : 1 + Real.log x ≤ (1 + Real.log 3) * (1 + Real.log M) := by
    nlinarith [mul_nonneg hlog3 hlogM]
  have hyLog : 1 + Real.log y ≤ (1 + Real.log 3) * (1 + Real.log M) := by
    nlinarith [mul_nonneg hlog3 hlogM]
  have hE : 1 + |b| + Real.log y ≤ (1 + |b| + Real.log 3) * (1 + Real.log M) := by
    nlinarith [mul_nonneg hlog3 hlogM, mul_nonneg (abs_nonneg b) hlogM]
  have hxErr := mul_le_mul_of_nonneg_left hxLog
    (Real.rpow_nonneg hx0.le (1 / 3 : ℝ))
  have hyErr := mul_le_mul hyPow hyLog hlogy0 (by positivity : 0 ≤ 3 * x ^ (1 / 3 : ℝ))
  have hmain := divisor_main_increment b x y hx0 hxy
  have hmain' := mul_le_mul_of_nonneg_left hE (sub_nonneg.mpr hxy)
  rw [divisor_window_difference x y hxy]
  have hSum := (abs_le.mp hxV).1
  have hSum' := (abs_le.mp hyV).2
  have hErr := mul_le_mul_of_nonneg_left (add_le_add hxErr hyErr) hC
  have hpos1 : 0 ≤ (y - x) * (4 * C * (1 + Real.log 3)) * (1 + Real.log M) := by positivity
  have hpos2 : 0 ≤ x ^ (1 / 3 : ℝ) * (1 + |b| + Real.log 3) * (1 + Real.log M) := by positivity
  nlinarith

/-- The bounded endpoint case in the short interval consequence of Voronoi on page 337. -/
theorem small_divisor_interval (x y : ℝ) (hx0 : 0 ≤ x) (hx : x < 1) (hy : y ≤ 3 * x) :
    ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (n.divisors.card : ℝ) ≤ 15 * x ^ (1 / 3 : ℝ) := by
  by_cases hxthird : 1 / 3 ≤ x
  · have hsub : Ioc ⌊x⌋₊ ⌊y⌋₊ ⊆ Icc 1 3 := by
      intro n hn
      have hnI := mem_Ioc.mp hn
      have hfloor : ⌊y⌋₊ ≤ 3 := by
        have hh := Nat.floor_mono (show y ≤ (3 : ℝ) by linarith)
        norm_num at hh
        exact hh
      exact mem_Icc.mpr ⟨by omega, hnI.2.trans hfloor⟩
    have hs := sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => (n.divisors.card : ℝ)) hsub
      (fun _ _ _ => by positivity)
    have hsum : (∑ n ∈ Icc 1 3, (n.divisors.card : ℝ)) = 5 := by
      norm_cast
    rw [hsum] at hs
    have hpow : x ≤ x ^ (1 / 3 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge (by linarith : 0 < x) hx.le
        (by norm_num : (1 / 3 : ℝ) ≤ 1)
    linarith
  · have hfloorx : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
    have hfloory : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp only [hfloorx, hfloory, Ioc_self, sum_empty]
    positivity

/-- The elementary short interval consequence of a summatory Voronoi bound on page 337.
This implication is CONDITIONAL ON the explicit summatory bound. -/
theorem short_divisor_interval_of_summatory (C b : ℝ) (hC : 0 ≤ C)
    (hV : ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) - (x * Real.log x + b * x)| ≤
        C * x ^ (1 / 3 : ℝ) * (1 + Real.log x)) :
    ∃ D : ℝ, 0 < D ∧ ∀ (M N : ℝ) (u : ℕ),
      2 ≤ M → 0 ≤ N → N ≤ 2 * M → 0 < u →
      ∑ v ∈ Ioc ⌊M / u⌋₊ ⌊(M + N) / u⌋₊, (v.divisors.card : ℝ) ≤
        D * (N / u + M ^ (1 / 3 : ℝ) * (u : ℝ) ^ (-(1 / 3) : ℝ)) *
          (1 + Real.log M) := by
  let A := 1 + |b| + Real.log 3 + 4 * C * (1 + Real.log 3)
  let D := 15 + A
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro M N u hM hN hNM hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hM0 : 0 ≤ M := by linarith
  let x := M / u
  let y := (M + N) / u
  have hx0 : 0 ≤ x := div_nonneg hM0 hu0.le
  have hxy : x ≤ y := by dsimp [x, y]; gcongr; linarith
  have hxM : x ≤ M := div_le_self hM0 hu1
  have hyx : y ≤ 3 * x := by
    dsimp [x, y]
    apply (div_le_iff₀ hu0).mpr
    field_simp
    nlinarith
  have hdiff : y - x = N / u := by dsimp [x, y]; ring
  have hdiff0 : 0 ≤ N / u := by positivity
  have hL1 : 1 ≤ 1 + Real.log M := by
    have := Real.log_nonneg (show 1 ≤ M by linarith)
    linarith
  have hp : x ^ (1 / 3 : ℝ) = M ^ (1 / 3 : ℝ) * (u : ℝ) ^ (-(1 / 3) : ℝ) := by
    dsimp [x]
    rw [Real.div_rpow hM0 hu0.le, Real.rpow_neg hu0.le, div_eq_mul_inv]
  change (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (n.divisors.card : ℝ)) ≤ _
  rw [← hp]
  by_cases hx : 1 ≤ x
  · have hh := large_divisor_interval_of_summatory C b M x y hC hM hx hxy hxM hyx
      (hV x hx) (hV y (hx.trans hxy))
    rw [hdiff] at hh
    apply hh.trans
    change A * (N / u + x ^ (1 / 3 : ℝ)) * (1 + Real.log M) ≤ _
    gcongr
    dsimp [D]
    linarith
  · have hh := small_divisor_interval x y hx0 (lt_of_not_ge hx) hyx
    calc
      _ ≤ 15 * x ^ (1 / 3 : ℝ) := hh
      _ ≤ D * x ^ (1 / 3 : ℝ) := by gcongr; dsimp [D]; linarith
      _ ≤ D * (N / u + x ^ (1 / 3 : ℝ)) := by gcongr; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL1

/-- Halupczok journal page 337, display 2.2 and the Voronoi estimate below it.
The summatory divisor error is O of x to one third times log x.
Taking its difference gives the short interval error M to one third times u to minus one third.
The factor 1 plus log M covers the bounded endpoint range M divided by u below 2.
No prime distribution estimate is used. -/
theorem short_divisor_interval :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N : ℝ) (u : ℕ),
      2 ≤ M → 0 ≤ N → N ≤ 2 * M → 0 < u →
      ∑ v ∈ Ioc ⌊M / u⌋₊ ⌊(M + N) / u⌋₊, (v.divisors.card : ℝ) ≤
        C * (N / u + M ^ (1 / 3 : ℝ) * (u : ℝ) ^ (-(1 / 3) : ℝ)) *
          (1 + Real.log M) := by
  obtain ⟨C, hC, hV⟩ := voronoi_divisor_sum
  exact short_divisor_interval_of_summatory C (2 * Real.eulerMascheroniConstant - 1) hC.le hV

/-- The interval membership change under factorization in page 337 display 2.2. -/
theorem factor_window_subset (M N : ℝ) (u B : ℕ) (hM : 0 ≤ M) (hN : 0 ≤ N) (hu : 0 < u) :
    (Icc 1 B).filter (fun v => u * v ∈ Ioc ⌊M⌋₊ ⌊M + N⌋₊) ⊆
      Ioc ⌊M / u⌋₊ ⌊(M + N) / u⌋₊ := by
  intro v hv
  obtain ⟨hvB, huv⟩ := mem_filter.mp hv
  obtain ⟨hlo, hhi⟩ := mem_Ioc.mp huv
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : M < (u : ℝ) * v := by
    exact_mod_cast (Nat.floor_lt hM).mp hlo
  have hupper : (u : ℝ) * v ≤ M + N := by
    have hh := (Nat.le_floor_iff (show 0 ≤ M + N by linarith)).mp hhi
    exact_mod_cast hh
  apply mem_Ioc.mpr
  constructor
  · exact (Nat.floor_lt (div_nonneg hM huR.le)).mpr ((div_lt_iff₀ huR).mpr (by nlinarith))
  · exact (Nat.le_floor_iff (div_nonneg (by nlinarith) huR.le)).mpr
      ((le_div_iff₀ huR).mpr (by nlinarith))

/-- Display 2.2 after summing the short divisor interval estimates.
This implication is CONDITIONAL ON the explicitly supplied short interval bound. -/
theorem interval_moment_of_short_bound (C M N : ℝ) (Q : ℕ)
    (hM : 2 ≤ M) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hshort : ∀ u ∈ Icc 1 Q,
      ∑ v ∈ Ioc ⌊M / u⌋₊ ⌊(M + N) / u⌋₊, (v.divisors.card : ℝ) ≤
        C * (N / u + M ^ (1 / 3 : ℝ) * (u : ℝ) ^ (-(1 / 3) : ℝ)) * (1 + Real.log M)) :
    ∑ s ∈ Ioc ⌊M⌋₊ ⌊M + N⌋₊,
        (((Icc 1 Q).filter (fun u => u ∣ s)).card : ℝ) ^ 2 ≤
      C * (N + M ^ (1 / 3 : ℝ) * (Q : ℝ) ^ (2 / 3 : ℝ)) *
        (1 + Real.log M) * (1 + Real.log Q) ^ 2 := by
  have hL : 0 ≤ 1 + Real.log M := by
    have := Real.log_nonneg (show 1 ≤ M by linarith)
    linarith
  have hfact := overlap_factor_bound (Ioc ⌊M⌋₊ ⌊M + N⌋₊) (Icc 1 Q) ⌊M + N⌋₊
    (fun s hs => ⟨by have := (mem_Ioc.mp hs).1; omega, (mem_Ioc.mp hs).2⟩)
    (fun u hu => (mem_Icc.mp hu).1)
  calc
    _ ≤ ∑ u ∈ Icc 1 Q, (u.divisors.card : ℝ) *
        ∑ v ∈ (Icc 1 ⌊M + N⌋₊).filter (fun v => u * v ∈ Ioc ⌊M⌋₊ ⌊M + N⌋₊),
          (v.divisors.card : ℝ) := hfact
    _ ≤ ∑ u ∈ Icc 1 Q, (u.divisors.card : ℝ) *
        (C * (N / u + M ^ (1 / 3 : ℝ) * (u : ℝ) ^ (-(1 / 3) : ℝ)) *
          (1 + Real.log M)) := by
      apply sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply le_trans _ (hshort u hu)
      exact sum_le_sum_of_subset_of_nonneg
        (factor_window_subset M N u _ (by linarith) hN (mem_Icc.mp hu).1)
        (fun _ _ _ => by positivity)
    _ = C * (1 + Real.log M) *
        (N * (∑ u ∈ Icc 1 Q, (u.divisors.card : ℝ) / u) +
          M ^ (1 / 3 : ℝ) * (∑ u ∈ Icc 1 Q,
            (u.divisors.card : ℝ) * (u : ℝ) ^ (-(1 / 3) : ℝ))) := by
      rw [mul_add, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ C * (1 + Real.log M) *
        (N * (1 + Real.log Q) ^ 2 + M ^ (1 / 3 : ℝ) *
          ((Q : ℝ) ^ (2 / 3 : ℝ) * (1 + Real.log Q) ^ 2)) := by
      gcongr
      · exact divisor_reciprocal_sum Q
      · exact divisor_third_sum Q
    _ = _ := by ring

/-- Absorb the Voronoi error at the level in Lemma 2.1 on page 336.
The doubled window permits M at most 3X. -/
theorem level_third_absorption {c R X Q M : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hX : 0 < X) (hQ0 : 0 ≤ Q) (hM0 : 0 ≤ M) (hM : M ≤ 3 * X)
    (hQ : Q ≤ c * R ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ)) :
    M ^ (1 / 3 : ℝ) * Q ^ (2 / 3 : ℝ) ≤ (3 * c ^ 2) ^ (1 / 3 : ℝ) * R := by
  have hs := pow_le_pow_left₀ hQ0 hQ 2
  have hRpow : (R ^ (3 / 2 : ℝ)) ^ 2 = R ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  have hXpow : (X ^ (-(1 / 2) : ℝ)) ^ 2 = X⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    norm_num [Real.rpow_neg_one]
  rw [mul_pow, mul_pow, hRpow, hXpow] at hs
  have hsq : Q ^ 2 * X ≤ c ^ 2 * R ^ 3 := by
    have := mul_le_mul_of_nonneg_right hs hX.le
    simpa [mul_assoc, hX.ne'] using this
  have hcub : (M ^ (1 / 3 : ℝ) * Q ^ (2 / 3 : ℝ)) ^ 3 ≤
      ((3 * c ^ 2) ^ (1 / 3 : ℝ) * R) ^ 3 := by
    have hMpow : (M ^ (1 / 3 : ℝ)) ^ 3 = M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]
      norm_num
    have hQpow : (Q ^ (2 / 3 : ℝ)) ^ 3 = Q ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0]
      norm_num
    have hcpow : ((3 * c ^ 2) ^ (1 / 3 : ℝ)) ^ 3 = 3 * c ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 3 * c ^ 2)]
      norm_num
    rw [mul_pow, mul_pow, hMpow, hQpow, hcpow]
    nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg Q)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp hcub

/-- Shift the doubled progression window to positive divisors on page 337 display 2.2. -/
theorem even_moment_le_interval (X R : ℝ) (a : ℤ) (Q : ℕ)
    (hX : 0 ≤ X) (hR : 0 ≤ R) (ha : (a : ℝ) ≤ X) :
    ∑ k ∈ kRange X R,
        (((Icc 1 Q).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
      ∑ s ∈ Ioc ⌊2 * X - a⌋₊ ⌊2 * X - a + 2 * R⌋₊,
        (((Icc 1 Q).filter (fun q => q ∣ s)).card : ℝ) ^ 2 := by
  let t : ℕ → ℕ := fun k => (((2 * k : ℕ) : ℤ) - a).toNat
  have hpos (k : ℕ) (hk : k ∈ kRange X R) : 0 ≤ ((2 * k : ℕ) : ℤ) - a := by
    have hkX := (mem_filter.mp hk).2.1
    have hh : (a : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast (sub_nonneg.mpr hh)
  have ht (k : ℕ) (hk : k ∈ kRange X R) : ((t k : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) - a :=
    Int.toNat_of_nonneg (hpos k hk)
  have hi : Set.InjOn t (kRange X R) := by
    intro k hk j hj he
    have heZ : ((t k : ℕ) : ℤ) = t j := by exact_mod_cast he
    rw [ht k hk, ht j hj] at heZ
    omega
  have hsub : (kRange X R).image t ⊆ Ioc ⌊2 * X - a⌋₊ ⌊2 * X - a + 2 * R⌋₊ := by
    intro s hs
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hs
    have hkI := (mem_filter.mp hk).2
    have htR : ((t k : ℕ) : ℝ) = 2 * (k : ℝ) - a := by exact_mod_cast ht k hk
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (show 0 ≤ 2 * X - a by linarith)).mpr
      rw [htR]
      linarith [hkI.1]
    · apply (Nat.le_floor_iff (show 0 ≤ 2 * X - a + 2 * R by linarith)).mpr
      rw [htR]
      linarith [hkI.2]
  have he (k : ℕ) (hk : k ∈ kRange X R) :
      (Icc 1 Q).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q]) =
        (Icc 1 Q).filter (fun q => q ∣ t k) := by
    apply filter_congr
    intro q _
    rw [← Int.natCast_dvd_natCast, ht k hk]
    rw [Int.modEq_iff_dvd, dvd_sub_comm]
  calc
    _ = ∑ s ∈ (kRange X R).image t, (((Icc 1 Q).filter (fun q => q ∣ s)).card : ℝ) ^ 2 := by
      rw [sum_image hi]
      apply sum_congr rfl
      intro k hk
      rw [he k hk]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

/-- Replace a polynomially bounded argument by log Y after page 337 display 2.2. -/
theorem polynomial_log_bound {T D Y : ℝ} (hD : 0 < D) (hY : Real.exp 1 ≤ Y)
    (hT : 0 < T) (hTD : T ≤ D * Y ^ 2) :
    1 + Real.log T ≤ (|Real.log D| + 3) * Real.log Y := by
  have hY0 : 0 < Y := (Real.exp_pos 1).trans_le hY
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hY
  have hh := Real.log_le_log hT hTD
  rw [Real.log_mul hD.ne' (by positivity), Real.log_pow] at hh
  norm_num at hh
  have hDlog := le_abs_self (Real.log D)
  have hmul := le_mul_of_one_le_right (abs_nonneg (Real.log D)) hL
  nlinarith

/-- The level of Lemma 2.1 is polynomially bounded, for logarithm comparison only. -/
theorem level_polynomial_bound {c R X Y Q : ℝ} (hc : 0 < c) (hR : 1 ≤ R)
    (hRY : R ≤ Y) (hYX : Y ≤ X)
    (hQ : Q ≤ c * R ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ)) :
    Q ≤ c * Y ^ 2 := by
  have hXp : X ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hR.trans (hRY.trans hYX)) (by norm_num)
  have hRp : R ^ (3 / 2 : ℝ) ≤ R ^ 2 := by
    exact_mod_cast (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (3 / 2 : ℝ) ≤ 2))
  have hRR : R ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (by linarith) hRY 2
  calc
    Q ≤ c * R ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ) := hQ
    _ ≤ c * R ^ (3 / 2 : ℝ) := by
      exact mul_le_of_le_one_right (by positivity) hXp
    _ ≤ c * R ^ 2 := mul_le_mul_of_nonneg_left hRp hc.le
    _ ≤ c * Y ^ 2 := mul_le_mul_of_nonneg_left hRR hc.le

/-- The fixed even overlap moment from page 337 display 2.2.
This assembly remains CONDITIONAL ON short_divisor_interval. -/
theorem fixed_even_moment (c K : ℝ) (hc : 0 < c) (hK : 0 < K) (a : ℤ) :
    ∃ C Y0 : ℝ, 0 < C ∧ ∀ X R Y Q : ℝ,
      Y0 ≤ Y → 1 ≤ R → R ≤ Y → Y ≤ X → X ≤ K * Y ^ 2 → (a : ℝ) ≤ X →
      1 ≤ Q → Q ≤ c * R ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ) →
      ∑ k ∈ kRange X R,
        (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
        C * R * Real.log Y ^ 3 := by
  obtain ⟨CV, hCV, hV⟩ := short_divisor_interval
  let D := (3 * c ^ 2) ^ (1 / 3 : ℝ)
  let LM := |Real.log (3 * K)| + 3
  let LQ := |Real.log c| + 3
  refine ⟨CV * (2 + D) * LM * LQ ^ 2, max (Real.exp 1) (max 2 |(a : ℝ)|), ?_, ?_⟩
  · dsimp [D, LM, LQ]
    positivity
  intro X R Y Q hY hR hRY hYX hXK ha hQ1 hQ
  have hYe : Real.exp 1 ≤ Y := (le_max_left _ _).trans hY
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have habs : |(a : ℝ)| ≤ X := (le_max_right _ _).trans
    (((le_max_right _ _).trans hY).trans hYX)
  have hX2 : 2 ≤ X := hY2.trans hYX
  have hR0 : 0 < R := by linarith
  have hX0 : 0 < X := by linarith
  let M := 2 * X - a
  have hMX : X ≤ M := by dsimp [M]; linarith
  have hM2 : 2 ≤ M := hX2.trans hMX
  have hM3 : M ≤ 3 * X := by
    dsimp [M]
    have := (neg_le_abs (a : ℝ)).trans habs
    linarith
  have hN : 2 * R ≤ 2 * M := by linarith
  have hq0 : (0 : ℝ) ≤ ⌊Q⌋₊ := Nat.cast_nonneg _
  have hqQ : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hq1 : 1 ≤ (⌊Q⌋₊ : ℝ) := by
    exact_mod_cast Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Q by simpa using hQ1)
  have hqlevel : (⌊Q⌋₊ : ℝ) ≤ c * R ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ) := hqQ.trans hQ
  have hMom := interval_moment_of_short_bound CV M (2 * R) ⌊Q⌋₊ hM2
    (by positivity) hCV.le (fun u hu => hV M (2 * R) u hM2 (by positivity) hN (mem_Icc.mp hu).1)
  have hErr := level_third_absorption hc hR0 hX0 hq0 (by linarith : 0 ≤ M) hM3 hqlevel
  have hA : 2 * R + M ^ (1 / 3 : ℝ) * (⌊Q⌋₊ : ℝ) ^ (2 / 3 : ℝ) ≤ (2 + D) * R := by
    dsimp [D]
    nlinarith
  have hlogM : 1 + Real.log M ≤ LM * Real.log Y :=
    polynomial_log_bound (by positivity : 0 < 3 * K) hYe (by linarith) (by nlinarith)
  have hqpoly : (⌊Q⌋₊ : ℝ) ≤ c * Y ^ 2 :=
    level_polynomial_bound hc hR hRY hYX hqlevel
  have hlogQ : 1 + Real.log (⌊Q⌋₊ : ℝ) ≤ LQ * Real.log Y :=
    polynomial_log_bound hc hYe (by linarith) hqpoly
  have hMlog0 : 0 ≤ 1 + Real.log M := by
    have := Real.log_nonneg (show 1 ≤ M by linarith)
    linarith
  have hQlog0 := one_add_log_nonneg ⌊Q⌋₊
  have hLY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  calc
    _ ≤ ∑ s ∈ Ioc ⌊M⌋₊ ⌊M + 2 * R⌋₊,
        (((Icc 1 ⌊Q⌋₊).filter (fun q => q ∣ s)).card : ℝ) ^ 2 :=
      even_moment_le_interval X R a ⌊Q⌋₊ hX0.le hR0.le ha
    _ ≤ CV * (2 * R + M ^ (1 / 3 : ℝ) * (⌊Q⌋₊ : ℝ) ^ (2 / 3 : ℝ)) *
        (1 + Real.log M) * (1 + Real.log (⌊Q⌋₊ : ℝ)) ^ 2 := hMom
    _ ≤ CV * ((2 + D) * R) * (LM * Real.log Y) * (LQ * Real.log Y) ^ 2 := by
      gcongr <;> dsimp [D, LM, LQ] <;> positivity
    _ = _ := by ring

/-- Finite complex Cauchy Schwarz for the progression filters of Lemma 2.1 on page 336. -/
theorem complex_filter_cauchy {ι κ : Type*} (W : Finset ι) (U : Finset κ)
    (p : κ → ι → Prop) [∀ q n, Decidable (p q n)] (w : ι → ℂ) :
    (∑ q ∈ U, ‖∑ n ∈ W.filter (p q), w n‖) ^ 2 ≤
      (∑ n ∈ W, ‖w n‖ ^ 2) * ∑ n ∈ W, ((U.filter (fun q => p q n)).card : ℝ) ^ 2 := by
  have htriangle : ∑ q ∈ U, ‖∑ n ∈ W.filter (p q), w n‖ ≤
      ∑ n ∈ W, ‖w n‖ * ((U.filter (fun q => p q n)).card : ℝ) := by
    calc
      _ ≤ ∑ q ∈ U, ∑ n ∈ W.filter (p q), ‖w n‖ := by
        exact sum_le_sum fun q _ => norm_sum_le _ _
      _ = ∑ n ∈ W, ‖w n‖ * ((U.filter (fun q => p q n)).card : ℝ) := by
        simp_rw [sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro n _
        rw [card_filter]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        split_ifs <;> simp
  have h0 : 0 ≤ ∑ q ∈ U, ‖∑ n ∈ W.filter (p q), w n‖ := sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ ≤ (∑ n ∈ W, ‖w n‖ * ((U.filter (fun q => p q n)).card : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := sum_mul_sq_le_sq_mul_sq W _ _
/-- Shift the progression window to positive divisors on page 337 display 2.2. -/
theorem residue_moment_le_interval (X R : ℝ) (a : ℤ) (Q : ℕ)
    (hX : 0 ≤ X) (hR : 0 ≤ R) (ha : (a : ℝ) ≤ X) :
    ∑ k ∈ kRange X R,
        (((Icc 1 Q).filter (fun q : ℕ => ((k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
      ∑ s ∈ Ioc ⌊X - a⌋₊ ⌊X - a + R⌋₊,
        (((Icc 1 Q).filter (fun q => q ∣ s)).card : ℝ) ^ 2 := by
  let t : ℕ → ℕ := fun k => (((k : ℕ) : ℤ) - a).toNat
  have hpos (k : ℕ) (hk : k ∈ kRange X R) : 0 ≤ ((k : ℕ) : ℤ) - a := by
    have hkX := (mem_filter.mp hk).2.1
    have hh : (a : ℝ) ≤ ((k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast (sub_nonneg.mpr hh)
  have ht (k : ℕ) (hk : k ∈ kRange X R) : ((t k : ℕ) : ℤ) = ((k : ℕ) : ℤ) - a :=
    Int.toNat_of_nonneg (hpos k hk)
  have hi : Set.InjOn t (kRange X R) := by
    intro k hk j hj he
    have heZ : ((t k : ℕ) : ℤ) = t j := by exact_mod_cast he
    rw [ht k hk, ht j hj] at heZ
    omega
  have hsub : (kRange X R).image t ⊆ Ioc ⌊X - a⌋₊ ⌊X - a + R⌋₊ := by
    intro s hs
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hs
    have hkI := (mem_filter.mp hk).2
    have htR : ((t k : ℕ) : ℝ) = (k : ℝ) - a := by exact_mod_cast ht k hk
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (show 0 ≤ X - a by linarith)).mpr
      rw [htR]
      linarith [hkI.1]
    · apply (Nat.le_floor_iff (show 0 ≤ X - a + R by linarith)).mpr
      rw [htR]
      linarith [hkI.2]
  have he (k : ℕ) (hk : k ∈ kRange X R) :
      (Icc 1 Q).filter (fun q : ℕ => ((k : ℕ) : ℤ) ≡ a [ZMOD q]) =
        (Icc 1 Q).filter (fun q => q ∣ t k) := by
    apply filter_congr
    intro q _
    rw [← Int.natCast_dvd_natCast, ht k hk]
    rw [Int.modEq_iff_dvd, dvd_sub_comm]
  calc
    _ = ∑ s ∈ (kRange X R).image t, (((Icc 1 Q).filter (fun q => q ∣ s)).card : ℝ) ^ 2 := by
      rw [sum_image hi]
      apply sum_congr rfl
      intro k hk
      rw [he k hk]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

/-- The complex coefficient form of Lemma 2.1 on page 336, squared.
The modulus range is full rather than dyadic and the logarithms are explicit.
The statement remains CONDITIONAL ON the single summatory Voronoi input. -/
theorem complex_progression_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (X R : ℝ) (Q : ℕ) (a : ℤ) (w : ℕ → ℂ),
      0 ≤ X → 2 ≤ X - a → 0 ≤ R → R ≤ 2 * (X - a) →
      (∑ q ∈ Icc 1 Q, ‖∑ n ∈ (kRange X R).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖) ^ 2 ≤
      (∑ n ∈ kRange X R, ‖w n‖ ^ 2) *
        (C * (R + (X - a) ^ (1 / 3 : ℝ) * (Q : ℝ) ^ (2 / 3 : ℝ)) *
          (1 + Real.log (X - a)) * (1 + Real.log Q) ^ 2) := by
  obtain ⟨C, hC, hV⟩ := short_divisor_interval
  refine ⟨C, hC, ?_⟩
  intro X R Q a w hX hM hR hRM
  have hMom := interval_moment_of_short_bound C (X - a) R Q hM hR hC.le
    (fun u hu => hV (X - a) R u hM hR hRM (mem_Icc.mp hu).1)
  have hShift := residue_moment_le_interval X R a Q hX hR (by linarith)
  have hCS := complex_filter_cauchy (kRange X R) (Icc 1 Q)
    (fun (q n : ℕ) => (n : ℤ) ≡ a [ZMOD q]) w
  exact hCS.trans (mul_le_mul_of_nonneg_left (hShift.trans hMom)
    (sum_nonneg fun _ _ => sq_nonneg _))

/-- The eventual natural dyadic form of page 336 Lemma 2.1, squared.
The fixed residue controls only the threshold. This remains CONDITIONAL ON Voronoi. -/
theorem lemma21_eventual_squared (a : ℤ) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ (X N : ℝ) (Q : ℕ) (w : ℕ → ℂ),
      X0 ≤ X → 0 ≤ N → N ≤ X → 1 ≤ Q → (Q : ℝ) ≤ X →
      (∑ q ∈ Ico Q (2 * Q), ‖∑ n ∈ (kRange X N).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖) ^ 2 ≤
        C * (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) *
          Real.log (X + 1) ^ 3 * ∑ n ∈ kRange X N, ‖w n‖ ^ 2 := by
  obtain ⟨CV, hCV, hb⟩ := complex_progression_bound
  let B := |Real.log (2 : ℝ)| + 3
  refine ⟨4 * CV * B ^ 3, max (Real.exp 1) (2 * |(a : ℝ)| + 4), ?_, ?_⟩
  · dsimp [B]; positivity
  intro X N Q w hX hN hNX hQ1 hQX
  have hXe : Real.exp 1 ≤ X := (le_max_left _ _).trans hX
  have hXa : 2 * |(a : ℝ)| + 4 ≤ X := (le_max_right _ _).trans hX
  have hX4 : 4 ≤ X := by nlinarith [abs_nonneg (a : ℝ)]
  have hX0 : 0 < X := by linarith
  let M := X - a
  have hM2 : 2 ≤ M := by
    dsimp [M]
    nlinarith [le_abs_self (a : ℝ)]
  have hXM : X ≤ 2 * M := by
    dsimp [M]
    nlinarith [le_abs_self (a : ℝ)]
  have hMupper : M ≤ 2 * X := by
    dsimp [M]
    nlinarith [neg_le_abs (a : ℝ)]
  have hE0 : 0 ≤ ∑ n ∈ kRange X N, ‖w n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hfull := hb X N (2 * Q) a w hX0.le hM2 hN (hNX.trans hXM)
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have h2Q1 : (1 : ℝ) ≤ (2 * Q : ℕ) := by exact_mod_cast (show 1 ≤ 2 * Q by omega)
  have h2Qpoly : ((2 * Q : ℕ) : ℝ) ≤ 2 * X ^ 2 := by
    push_cast
    nlinarith
  have hMpoly : M ≤ 2 * X ^ 2 := by nlinarith
  have hLM : 1 + Real.log M ≤ B * Real.log X :=
    polynomial_log_bound (by norm_num : (0 : ℝ) < 2) hXe (by linarith) hMpoly
  have hLQ : 1 + Real.log ((2 * Q : ℕ) : ℝ) ≤ B * Real.log X :=
    polynomial_log_bound (by norm_num : (0 : ℝ) < 2) hXe (by linarith) h2Qpoly
  have hMpow : M ^ (1 / 3 : ℝ) ≤ 2 * X ^ (1 / 3 : ℝ) := by
    calc
      _ ≤ (2 * X) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by linarith) hMupper (by norm_num)
      _ = (2 : ℝ) ^ (1 / 3 : ℝ) * X ^ (1 / 3 : ℝ) := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 3 : ℝ) ≤ 1) using 1 <;> norm_num
  have hQpow : ((2 * Q : ℕ) : ℝ) ^ (2 / 3 : ℝ) ≤ 2 * (Q : ℝ) ^ (2 / 3 : ℝ) := by
    push_cast
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hQ0]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (2 / 3 : ℝ) ≤ 1) using 1 <;> norm_num
  have herr : N + M ^ (1 / 3 : ℝ) * ((2 * Q : ℕ) : ℝ) ^ (2 / 3 : ℝ) ≤
      4 * (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) := by
    have hh := mul_le_mul hMpow hQpow (by positivity) (by positivity)
    nlinarith
  have hlogM0 : 0 ≤ 1 + Real.log M := by
    have := Real.log_nonneg (show 1 ≤ M by linarith)
    linarith
  have hlogQ0 := one_add_log_nonneg (2 * Q)
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogXX : Real.log X ≤ Real.log (X + 1) := Real.log_le_log hX0 (by linarith)
  have hsub : Ico Q (2 * Q) ⊆ Icc 1 (2 * Q) := by
    intro q hq
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hq
    exact mem_Icc.mpr ⟨hQ1.trans hlo, by omega⟩
  have hs := sum_le_sum_of_subset_of_nonneg
    (f := fun q : ℕ => ‖∑ n ∈ (kRange X N).filter
      (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖) hsub (fun _ _ _ => norm_nonneg _)
  have hs0 : 0 ≤ ∑ q ∈ Ico Q (2 * Q), ‖∑ n ∈ (kRange X N).filter
      (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖ := sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ ≤ (∑ q ∈ Icc 1 (2 * Q), ‖∑ n ∈ (kRange X N).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖) ^ 2 := by gcongr
    _ ≤ (∑ n ∈ kRange X N, ‖w n‖ ^ 2) *
        (CV * (N + M ^ (1 / 3 : ℝ) * ((2 * Q : ℕ) : ℝ) ^ (2 / 3 : ℝ)) *
          (1 + Real.log M) * (1 + Real.log ((2 * Q : ℕ) : ℝ)) ^ 2) := hfull
    _ ≤ (∑ n ∈ kRange X N, ‖w n‖ ^ 2) *
        (CV * (4 * (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ))) *
          (B * Real.log X) * (B * Real.log X) ^ 2) := by
      gcongr <;> dsimp [B] <;> positivity
    _ = 4 * CV * B ^ 3 * (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) *
        Real.log X ^ 3 * ∑ n ∈ kRange X N, ‖w n‖ ^ 2 := by ring
    _ ≤ _ := by
      gcongr <;> dsimp [B] <;> positivity

/-- Page 336 display 2.1 in its eventual natural Q form.
The square root factors and the logarithmic exponent three halves are explicit.
This remains CONDITIONAL ON the single Voronoi asymptotic leaf. -/
theorem lemma21_eventual (a : ℤ) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ (X N : ℝ) (Q : ℕ) (w : ℕ → ℂ),
      X0 ≤ X → 0 ≤ N → N ≤ X → 1 ≤ Q → (Q : ℝ) ≤ X →
      (∑ q ∈ Ico Q (2 * Q), ‖∑ n ∈ (kRange X N).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖) ≤
        C * Real.sqrt (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) *
          Real.log (X + 1) ^ (3 / 2 : ℝ) * Real.sqrt (∑ n ∈ kRange X N, ‖w n‖ ^ 2) := by
  obtain ⟨C, X0, hC, hb⟩ := lemma21_eventual_squared a
  refine ⟨Real.sqrt C, max X0 1, Real.sqrt_pos.mpr hC, ?_⟩
  intro X N Q w hX hN hNX hQ1 hQX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  have hS : 0 ≤ N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ) := by positivity
  have hE : 0 ≤ ∑ n ∈ kRange X N, ‖w n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hh := hb X N Q w ((le_max_left _ _).trans hX) hN hNX hQ1 hQX
  have hpow : (Real.log (X + 1) ^ (3 / 2 : ℝ)) ^ 2 = Real.log (X + 1) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  have he : (Real.sqrt C * Real.sqrt (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) *
      Real.log (X + 1) ^ (3 / 2 : ℝ) * Real.sqrt (∑ n ∈ kRange X N, ‖w n‖ ^ 2)) ^ 2 =
      C * (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) *
        Real.log (X + 1) ^ 3 * ∑ n ∈ kRange X N, ‖w n‖ ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC.le, Real.sq_sqrt hS, Real.sq_sqrt hE, hpow]
  rw [← he] at hh
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by positivity) hh

end LeanLab.Halupczok2012.Decomp532a
