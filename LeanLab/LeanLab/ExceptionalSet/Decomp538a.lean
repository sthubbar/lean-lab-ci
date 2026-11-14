/-
Karacuba 1971, Trudy MIAN 112, page244 Lemma3 and pages245 to248.
Helpers for task538. This file does not import KaracubaSplit.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.ExceptionalSet.Decomp1539a
import LeanLab.PNTPort.Vinogradov.Basic

namespace LeanLab.ExceptionalSet.Decomp538a

/-- The summands in page244 Lemma3 are bounded by their cap. -/
theorem capped_sum_le {ι : Type*} (s : Finset ι) (U : ℝ) (d : ι → ℝ) :
    ∑ x ∈ s, min U (1 / d x) ≤ s.card * U := by
  calc _ ≤ ∑ _x ∈ s, U := Finset.sum_le_sum fun _ _ => min_le_left _ _
    _ = s.card * U := by simp

/-- The case q one of page244 Lemma3 follows from the cap alone. -/
theorem capped_sum_unit (U : ℝ) (P : ℕ) (d : ℕ → ℝ) (hU : 0 < U) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / d x) ≤ 6 * U * ((P : ℝ) + 1) := by
  have h := capped_sum_le (Finset.Icc 1 P) U d
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
  nlinarith [Nat.cast_nonneg (α := ℝ) P]

/-- Two allowed phases in a q block need not be separated by one over twice q.
This is a route check for page244 Lemma3, not a counterexample to that lemma. -/
theorem full_block_spacing_counterexample :
    Int.gcd (1 : ℤ) 5 = 1 ∧ |(1 : ℝ)| ≤ 1 ∧
    |((1 : ℝ) / 5 + 1 / 5 ^ 2) * (5 - 1) -
      round (((1 : ℝ) / 5 + 1 / 5 ^ 2) * (5 - 1))| < 1 / (2 * 5) := by
  norm_num [round_eq, Int.floor_eq_iff]

/-- At most two distinct integers fit into a real interval of length strictly below two.
This is the cell count used for the rational grid in page244 Lemma3. -/
theorem card_le_two_of_integer_diameter {ι : Type*} (s : Finset ι) (t : ι → ℤ)
    (hinj : Set.InjOn t s) (hd : ∀ x ∈ s, ∀ y ∈ s, |(t x : ℝ) - t y| < 2) :
    s.card ≤ 2 := by
  classical
  by_cases hs : s.Nonempty
  · let m := (s.image t).min' (hs.image t)
    have hmem : m ∈ s.image t := Finset.min'_mem _ _
    obtain ⟨x, hx, htx⟩ := Finset.mem_image.mp hmem
    have hsub : s.image t ⊆ Finset.Icc m (m + 1) := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      have hmin : m ≤ t y := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      have hlt := (abs_lt.mp (hd y hy x hx)).2
      rw [htx] at hlt
      have hreal : (t y : ℝ) < (m : ℝ) + 2 := by linarith
      have hint : t y < m + 2 := by exact_mod_cast hreal
      exact Finset.mem_Icc.mpr ⟨hmin, by omega⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at hcard
    have heq : (m + 1 + 1 - m).toNat = 2 := by omega
    simpa only [Int.card_Icc, heq] using hcard
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- A cell of width one over q contains at most two perturbed rational grid points.
This replaces the false full block separation shortcut for page244 Lemma3. -/
theorem rational_cell_card_le_two (a : ℤ) (q : ℕ) (θ β : ℝ) (hq : 0 < q)
    (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) (j : ℤ) :
    ((Finset.range q).filter (fun x : ℕ =>
      ⌊(q : ℝ) * Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β)⌋ = j)).card ≤ 2 := by
  classical
  let f : ℕ → ℝ := fun x => (a / q + θ / (q : ℝ) ^ 2) * x + β
  let t : ℕ → ℤ := fun x => a * x - q * ⌊f x⌋
  let s := (Finset.range q).filter (fun x => ⌊(q : ℝ) * Int.fract (f x)⌋ = j)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hxy : ∀ x ∈ s, ∀ y ∈ s, |(x : ℝ) - y| < q := by
    intro x hx y hy
    have hxq : x < q := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hyq : y < q := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have hxr : (x : ℝ) < q := by exact_mod_cast hxq
    have hyr : (y : ℝ) < q := by exact_mod_cast hyq
    rw [abs_lt]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) x, Nat.cast_nonneg (α := ℝ) y]
  apply card_le_two_of_integer_diameter s t
  · intro x hx y hy ht
    have hprod : (q : ℤ) ∣ a * ((x : ℤ) - y) := by
      refine ⟨⌊f x⌋ - ⌊f y⌋, ?_⟩
      dsimp [t] at ht
      linear_combination ht
    have hdiv : (q : ℤ) ∣ (x : ℤ) - y :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hprod (by rwa [Int.gcd_comm])
    have hxq : x < q := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hyq : y < q := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    by_cases hle : x ≤ y
    · have hdiv' : (q : ℤ) ∣ (y : ℤ) - x := by
        convert (dvd_neg.mpr hdiv) using 1 <;> ring
      have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hdiv'
      omega
    · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hdiv
      omega
  · intro x hx y hy
    have hfx := (Finset.mem_filter.mp hx).2
    have hfy := (Finset.mem_filter.mp hy).2
    have hxlo := Int.floor_le ((q : ℝ) * Int.fract (f x))
    have hxhi := Int.lt_floor_add_one ((q : ℝ) * Int.fract (f x))
    have hylo := Int.floor_le ((q : ℝ) * Int.fract (f y))
    have hyhi := Int.lt_floor_add_one ((q : ℝ) * Int.fract (f y))
    rw [hfx] at hxlo hxhi
    rw [hfy] at hylo hyhi
    have hcell : |(q : ℝ) * (Int.fract (f x) - Int.fract (f y))| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith
    have hdrift : |θ / (q : ℝ) * ((x : ℝ) - y)| < 1 := by
      rw [abs_mul, abs_div, abs_of_pos hqr, div_mul_eq_mul_div, div_lt_one hqr]
      exact (mul_le_mul_of_nonneg_right hθ (abs_nonneg _)).trans_lt (by simpa using hxy x hx y hy)
    have hid : (t x : ℝ) - t y =
        (q : ℝ) * (Int.fract (f x) - Int.fract (f y)) - θ / q * ((x : ℝ) - y) := by
      simp only [t, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.fract, f]
      field_simp
      <;> ring
    rw [hid]
    exact (abs_sub _ _).trans_lt (by linarith)

/-- The harmonic tail in the cell proof of page244 Lemma3 fits into its logarithmic term. -/
theorem harmonic_tail_le_log (q : ℕ) (hq : 2 ≤ q) :
    (harmonic (q - 2) : ℝ) ≤ (3 / 2 : ℝ) * Real.log q := by
  have hl2 := Real.log_two_gt_d9
  have hl3 := Real.log_three_gt_d9
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  by_cases hbig : 8 ≤ q
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hqsub : (0 : ℝ) < (q - 2 : ℕ) := by exact_mod_cast (by omega : 0 < q - 2)
    have hmono : Real.log (q - 2 : ℕ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log hqsub (by exact_mod_cast Nat.sub_le q 2)
    have hl8 : Real.log (8 : ℝ) ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hbig)
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow] at hl8
    norm_num at hl8
    have hh := harmonic_le_one_add_log (q - 2)
    nlinarith
  · have hsmall : q ≤ 7 := by omega
    have hl5 : Real.log (4 : ℝ) ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    have hl7 : Real.log (6 : ℝ) ≤ Real.log 7 := Real.log_le_log (by norm_num) (by norm_num)
    interval_cases q <;> norm_num [harmonic, Finset.sum_range_succ] <;> nlinarith

/-- Summing both sides of the rational grid gives twice a harmonic sum.
This is the elementary summation in page244 Lemma3. -/
theorem reciprocal_grid_sum (q : ℕ) (hq : 2 ≤ q) :
    ∑ j ∈ Finset.Icc 1 (q - 2),
      ((q : ℝ) / j + (q : ℝ) / (q - 1 - j : ℕ)) =
        2 * q * (harmonic (q - 2) : ℝ) := by
  have hreflect : ∑ j ∈ Finset.Icc 1 (q - 2), (1 : ℝ) / (q - 1 - j : ℕ) =
      ∑ j ∈ Finset.Icc 1 (q - 2), (1 : ℝ) / j := by
    apply Finset.sum_bij (fun j _ => q - 1 - j)
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj k hk heq
      simp only [Finset.mem_Icc] at hj hk
      omega
    · intro j hj
      refine ⟨q - 1 - j, ?_, ?_⟩ <;> simp only [Finset.mem_Icc] at hj ⊢ <;> omega
    · intro j hj
      rfl
  have hh : ∑ j ∈ Finset.Icc 1 (q - 2), (1 : ℝ) / j = (harmonic (q - 2) : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [one_div, Rat.cast_inv, Rat.cast_natCast]
  simp only [one_div] at hreflect hh
  simp only [div_eq_mul_inv]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hreflect, hh]
  ring

/-- A grid cell controls a capped reciprocal distance by the two reciprocal grid endpoints.
The two endpoint cells use U itself, as in page244 Lemma3. -/
theorem capped_reciprocal_cell (U z : ℝ) (q j : ℕ) (hq : 2 ≤ q) (hj : j < q)
    (hcell : ⌊(q : ℝ) * Int.fract z⌋ = (j : ℤ)) :
    min U (1 / min (Int.fract z) (1 - Int.fract z)) ≤
      if j = 0 ∨ j = q - 1 then U else (q : ℝ) / j + (q : ℝ) / (q - 1 - j : ℕ) := by
  by_cases he : j = 0 ∨ j = q - 1
  · rw [if_pos he]
    exact min_le_left _ _
  · rw [if_neg he]
    have hjpos : 0 < j := by omega
    have hdpos : 0 < q - 1 - j := by omega
    have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hjr : (0 : ℝ) < j := by exact_mod_cast hjpos
    have hdr : (0 : ℝ) < (q - 1 - j : ℕ) := by exact_mod_cast hdpos
    have hlo := Int.floor_le ((q : ℝ) * Int.fract z)
    have hhi := Int.lt_floor_add_one ((q : ℝ) * Int.fract z)
    rw [hcell] at hlo hhi
    push_cast at hlo hhi
    have hcast : ((q - 1 - j : ℕ) : ℝ) = q - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    have hfpos : 0 < Int.fract z := by nlinarith
    have hgpos : 0 < 1 - Int.fract z := by linarith [Int.fract_lt_one z]
    have ha : 1 / Int.fract z ≤ (q : ℝ) / j := by
      apply (div_le_div_iff₀ hfpos hjr).mpr
      nlinarith
    have hb : 1 / (1 - Int.fract z) ≤ (q : ℝ) / (q - 1 - j : ℕ) := by
      apply (div_le_div_iff₀ hgpos hdr).mpr
      rw [hcast]
      nlinarith
    apply (min_le_right _ _).trans
    rcases le_total (Int.fract z) (1 - Int.fract z) with h | h
    · rw [min_eq_left h]
      exact ha.trans (le_add_of_nonneg_right (by positivity))
    · rw [min_eq_right h]
      exact hb.trans (le_add_of_nonneg_left (by positivity))

/-- The sharper grid bound reserves two additional caps for integer phases.
Source page244 Lemma3 and page246 display6. -/
theorem capped_sum_of_cell_count_sharp {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (U : ℝ) (q : ℕ) (hU : 0 < U) (hq : 2 ≤ q)
    (hcount : ∀ j : ℕ, (s.filter (fun x => ⌊(q : ℝ) * Int.fract (f x)⌋₊ = j)).card ≤ 2) :
    ∑ x ∈ s, min U (1 / min (Int.fract (f x)) (1 - Int.fract (f x))) ≤
      4 * U + 4 * q * (harmonic (q - 2) : ℝ) := by
  classical
  let b : ι → ℕ := fun x => ⌊(q : ℝ) * Int.fract (f x)⌋₊
  let w : ℕ → ℝ := fun j => if j = 0 ∨ j = q - 1 then U else
    (q : ℝ) / j + (q : ℝ) / (q - 1 - j : ℕ)
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hb : ∀ x ∈ s, b x ∈ Finset.range q := by
    intro x _
    rw [Finset.mem_range]
    apply (Nat.floor_lt (by positivity)).mpr
    exact mul_lt_of_lt_one_right hqr (Int.fract_lt_one _)
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    split_ifs <;> positivity
  have hfiber : ∀ j ∈ Finset.range q,
      ∑ x ∈ s.filter (fun x => b x = j),
        min U (1 / min (Int.fract (f x)) (1 - Int.fract (f x))) ≤ 2 * w j := by
    intro j hj
    calc _ ≤ ∑ _x ∈ s.filter (fun x => b x = j), w j := by
            apply Finset.sum_le_sum
            intro x hx
            have hbval := (Finset.mem_filter.mp hx).2
            have hint : ⌊(q : ℝ) * Int.fract (f x)⌋ = (j : ℤ) := by
              rw [← Int.natCast_floor_eq_floor (by positivity), show ⌊(q : ℝ) * Int.fract (f x)⌋₊ = j from hbval]
            exact capped_reciprocal_cell U (f x) q j hq (Finset.mem_range.mp hj) hint
      _ ≤ 2 * w j := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount j) (hw j)
  have hset : Finset.range q = insert 0 (insert (q - 1) (Finset.Icc 1 (q - 2))) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hz : 0 ∉ insert (q - 1) (Finset.Icc 1 (q - 2)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have he : q - 1 ∉ Finset.Icc 1 (q - 2) := by
    simp only [Finset.mem_Icc]
    omega
  have hwsum : ∑ j ∈ Finset.range q, w j = 2 * U + 2 * q * (harmonic (q - 2) : ℝ) := by
    rw [hset, Finset.sum_insert hz, Finset.sum_insert he]
    have hzval : w 0 = U := by simp [w]
    have heval : w (q - 1) = U := by simp [w]
    have hi : ∑ j ∈ Finset.Icc 1 (q - 2), w j =
        ∑ j ∈ Finset.Icc 1 (q - 2), ((q : ℝ) / j + (q : ℝ) / (q - 1 - j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have : ¬ (j = 0 ∨ j = q - 1) := by
        have := Finset.mem_Icc.mp hj
        omega
      simp only [w, if_neg this]
    rw [hzval, heval, hi, reciprocal_grid_sum q hq]
    ring
  have hsum : ∑ x ∈ s, min U (1 / min (Int.fract (f x)) (1 - Int.fract (f x))) ≤
      4 * U + 4 * q * (harmonic (q - 2) : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hb]
    calc _ ≤ ∑ j ∈ Finset.range q, 2 * w j := Finset.sum_le_sum hfiber
      _ = _ := by rw [← Finset.mul_sum, hwsum]; ring
  exact hsum


/-- A family with at most two points per rational grid cell satisfies the one block
bound of page244 Lemma3. -/
theorem capped_sum_of_cell_count {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (U : ℝ) (q : ℕ) (hU : 0 < U) (hq : 2 ≤ q)
    (hcount : ∀ j : ℕ, (s.filter (fun x => ⌊(q : ℝ) * Int.fract (f x)⌋₊ = j)).card ≤ 2) :
    ∑ x ∈ s, min U (1 / min (Int.fract (f x)) (1 - Int.fract (f x))) ≤
      6 * (U + q * Real.log q) := by
  have hsum := capped_sum_of_cell_count_sharp s f U q hU hq hcount
  have htail := mul_le_mul_of_nonneg_left (harmonic_tail_le_log q hq)
    (by positivity : (0 : ℝ) ≤ 4 * q)
  nlinarith

/-- The one block bound for the perturbed rational phase of page244 Lemma3. -/
theorem rational_block_bound (U : ℝ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.range q,
      min U (1 / min (Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β))
        (1 - Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β))) ≤
          6 * (U + q * Real.log q) := by
  apply capped_sum_of_cell_count (Finset.range q)
    (fun x : ℕ => (a / q + θ / (q : ℝ) ^ 2) * x + β) U q hU hq
  intro j
  apply (Finset.card_le_card ?_).trans
    (rational_cell_card_le_two a q θ β (by omega) hgcd hθ (j : ℤ))
  intro x hx
  obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hx, ?_⟩
  rw [← Int.natCast_floor_eq_floor (by positivity), heq]

/-- Karacuba page244 Lemma3, with the real quotient P over q.
The proof pads to whole q blocks and applies the two point cell bound. -/
theorem karacuba_lemma3 (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 1 ≤ q) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.Icc 1 P,
      min U (1 / min (Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β))
        (1 - Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β))) ≤
          6 * (U + q * Real.log q) * ((P : ℝ) / q + 1) := by
  by_cases hq1 : q = 1
  · subst q
    simpa using capped_sum_unit U P
      (fun x => min (Int.fract (((a : ℝ) + θ) * x + β))
        (1 - Int.fract (((a : ℝ) + θ) * x + β))) hU
  have hq2 : 2 ≤ q := by omega
  let α : ℝ := a / q + θ / (q : ℝ) ^ 2
  let f : ℕ → ℝ := fun x => min U (1 / min (Int.fract (α * (x + 1) + β))
    (1 - Int.fract (α * (x + 1) + β)))
  let C : ℝ := 6 * (U + q * Real.log q)
  have hC : 0 ≤ C := by
    have hl : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    dsimp [C]
    positivity
  have hb : ∀ b : ℕ, ∑ r ∈ Finset.range q, f (q * b + r) ≤ C := by
    intro b
    have hid : ∀ r : ℕ, α * ((q * b + r : ℕ) + 1) + β =
        α * r + (β + α * ((q * b : ℕ) + 1)) := by
      intro r
      push_cast
      ring
    dsimp only [f]
    simp_rw [hid]
    exact rational_block_bound U a q θ (β + α * ((q * b : ℕ) + 1)) hU hq2 hgcd hθ
  have hblocks : ∀ L : ℕ, ∑ x ∈ Finset.range (q * L), f x ≤ L * C := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Nat.mul_succ, Finset.sum_range_add]
      have := hb L
      push_cast
      nlinarith
  have hpad : P ≤ q * (P / q + 1) := by
    have hmod := Nat.mod_lt P (by omega : 0 < q)
    have hdiv := Nat.mod_add_div P q
    nlinarith
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    exact le_min hU.le (div_nonneg zero_le_one
      (le_min (Int.fract_nonneg _) (by linarith [Int.fract_lt_one (α * (x + 1) + β)])))
  have hI : ∑ x ∈ Finset.Icc 1 P,
      min U (1 / min (Int.fract (α * x + β)) (1 - Int.fract (α * x + β))) =
      ∑ x ∈ Finset.range P, f x := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, f, Nat.cast_add, Nat.cast_one]
    congr 1
    ext x
    simp only [add_comm]
  change ∑ x ∈ Finset.Icc 1 P,
      min U (1 / min (Int.fract (α * x + β)) (1 - Int.fract (α * x + β))) ≤ C * _
  rw [hI]
  calc _ ≤ ∑ x ∈ Finset.range (q * (P / q + 1)), f x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hpad) (fun x _ _ => hfn x)
    _ ≤ ((P / q + 1 : ℕ) : ℝ) * C := hblocks _
    _ ≤ C * ((P : ℝ) / q + 1) := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left ?_ hC
      push_cast
      have hd : ((P / q : ℕ) : ℝ) ≤ (P : ℝ) / q := Nat.cast_div_le
      linarith



/-- The Taylor polynomial at the left endpoint uses the ordinary derivatives. Source page245 before display4. -/
theorem taylor_left_endpoint (f : ℝ → ℝ) (n : ℕ) (a b : ℝ) (hab : a < b)
    (ha : ContDiffAt ℝ n f a) :
    taylorWithinEval f n (Set.Icc a b) a b = f a +
      ∑ j ∈ Finset.Icc 1 n, iteratedDeriv j f a / (j.factorial : ℝ) * (b - a) ^ j := by
  rw [taylor_within_apply]
  have ht : ∀ j ∈ Finset.range (n + 1),
      ((j.factorial : ℝ)⁻¹ * (b - a) ^ j) • iteratedDerivWithin j f (Set.Icc a b) a =
        iteratedDeriv j f a / (j.factorial : ℝ) * (b - a) ^ j := by
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (ha.of_le (by exact_mod_cast hjn)) (by exact ⟨le_rfl, hab.le⟩)]
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl ht]
  have hset : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp

/-- The normalized derivative bound controls the Taylor remainder. Source page245 before display4. Reuses the Mathlib Lagrange remainder. -/
theorem taylor_remainder_bound (f : ℝ → ℝ) (n : ℕ) (a h D : ℝ) (hh : 0 ≤ h)
    (hsm : ∃ U : Set ℝ, IsOpen U ∧ Set.Icc a (a + h) ⊆ U ∧ ContDiffOn ℝ (n + 1 : ℕ) f U)
    (hD : ∀ x ∈ Set.Icc a (a + h),
      |iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℝ)| ≤ D) :
    |f (a + h) - (f a + ∑ j ∈ Finset.Icc 1 n,
      iteratedDeriv j f a / (j.factorial : ℝ) * h ^ j)| ≤ D * h ^ (n + 1) := by
  by_cases hzero : h = 0
  · subst h
    have hsum : ∑ j ∈ Finset.Icc 1 n, iteratedDeriv j f a / (j.factorial : ℝ) * (0 : ℝ) ^ j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
      simp [hj0]
    simp [hsum]
  have hpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hzero)
  obtain ⟨U, hU, hsub, hf⟩ := hsm
  have haU : U ∈ nhds a := hU.mem_nhds (hsub ⟨le_rfl, by linarith⟩)
  have hca := hf.contDiffAt haU
  have hfn : ContDiffOn ℝ (n + 1 : ℕ) f (Set.uIcc a (a + h)) := by
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)]
    exact hf.mono hsub
  obtain ⟨ξ, hξ, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (by linarith : a ≠ a + h) hfn
  rw [Set.uIoo_of_lt (by linarith : a < a + h)] at hξ
  have hξD := hD ξ ⟨hξ.1.le, hξ.2.le⟩
  rw [Set.uIcc_of_le (by linarith : a ≤ a + h),
    taylor_left_endpoint f n a (a + h) (by linarith)
      (hca.of_le (by exact_mod_cast Nat.le_succ n)), add_sub_cancel_left] at heq
  rw [heq]
  calc _ = |iteratedDeriv (n + 1) f ξ / ((n + 1).factorial : ℝ)| * h ^ (n + 1) := by
          rw [show iteratedDeriv (n + 1) f ξ * h ^ (n + 1) / ((n + 1).factorial : ℝ) =
            (iteratedDeriv (n + 1) f ξ / ((n + 1).factorial : ℝ)) * h ^ (n + 1) by ring]
          rw [abs_mul, abs_of_nonneg (pow_nonneg hh _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hξD (pow_nonneg hh _)



/-- The paper choice of P2 turns the Taylor remainder scale into P to minus one over n squared. Source page245 before display4. -/
theorem taylor_scale_bound (c1 : ℝ) (n P : ℕ) (hn : 0 < n) (hP : 0 < P) :
    (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) *
      (⌊(P : ℝ) ^ (c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))))⌋₊ : ℝ) ^ (2 * (n + 1)) ≤
        (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let e : ℝ := c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))
  have hfloor : (⌊(P : ℝ) ^ e⌋₊ : ℝ) ≤ (P : ℝ) ^ e :=
    Nat.floor_le (Real.rpow_nonneg hPr.le _)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) ⌊(P : ℝ) ^ e⌋₊)
    hfloor (2 * (n + 1))
  have hexp : -(c1 * ((n + 1 : ℕ) : ℝ)) + e * ((2 * (n + 1) : ℕ) : ℝ) =
      -(1 / (n : ℝ) ^ 2) := by
    dsimp [e]
    push_cast
    field_simp
    <;> ring
  calc _ ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * ((P : ℝ) ^ e) ^ (2 * (n + 1)) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hPr.le _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hPr.le, ← Real.rpow_add hPr, hexp]


open LeanLab.ExceptionalSet.U1539

/-- The phase exponential is Lipschitz with constant two pi. Source page245 before display4. -/
theorem eC_norm_sub_le (x y : ℝ) : ‖eC x - eC y‖ ≤ 2 * Real.pi * |x - y| := by
  have heq : eC x - eC y = eC y * (Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) - 1) := by
    rw [mul_sub, mul_one]
    unfold eC
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul, norm_eC, one_mul]
  calc _ ≤ ‖2 * Real.pi * (x - y)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |x - y| := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]

/-- The double sum Taylor error from page245 display4, with a general normalized derivative cap.
Every evaluation point is inside the stated smooth interval. -/
theorem taylor_double_sum_bound (f : ℝ → ℝ) (n N P a M : ℕ) (D : ℝ)
    (hsm : ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧
      ContDiffOn ℝ (n + 1 : ℕ) f U)
    (hD : ∀ x ∈ Set.Icc (N : ℝ) (N + P),
      |iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℝ)| ≤ D)
    (ha : N ≤ a) (haP : a + M ^ 2 ≤ N + P) :
    ‖(∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      eC (f ((a + y * z : ℕ) : ℝ))) -
      ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
          iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖ ≤
      2 * Real.pi * ((M : ℝ) + 1) ^ 2 * (D * (M : ℝ) ^ (2 * (n + 1))) := by
  have hNa : (N : ℝ) ≤ a := by exact_mod_cast ha
  have haMr : (a : ℝ) + (M : ℝ) ^ 2 ≤ N + P := by exact_mod_cast haP
  have hDa := hD a ⟨hNa, by nlinarith [sq_nonneg (M : ℝ)]⟩
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hDa
  have hterm : ∀ y ∈ Finset.range (M + 1), ∀ z ∈ Finset.range (M + 1),
      ‖eC (f ((a + y * z : ℕ) : ℝ)) -
        eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
          iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖ ≤
          2 * Real.pi * (D * (M : ℝ) ^ (2 * (n + 1))) := by
    intro y hy z hz
    have hyM : y ≤ M := by have := Finset.mem_range.mp hy; omega
    have hzM : z ≤ M := by have := Finset.mem_range.mp hz; omega
    have hyz : ((y * z : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
      exact_mod_cast (show y * z ≤ M ^ 2 by simpa only [pow_two] using Nat.mul_le_mul hyM hzM)
    have hinterval : Set.Icc (a : ℝ) (a + ((y * z : ℕ) : ℝ)) ⊆ Set.Icc (N : ℝ) (N + P) := by
      intro x hx
      exact ⟨hNa.trans hx.1, hx.2.trans (by linarith)⟩
    have hsmall : ∃ U : Set ℝ, IsOpen U ∧
        Set.Icc (a : ℝ) (a + ((y * z : ℕ) : ℝ)) ⊆ U ∧ ContDiffOn ℝ (n + 1 : ℕ) f U := by
      obtain ⟨U, hU, hsub, hf⟩ := hsm
      exact ⟨U, hU, hinterval.trans hsub, hf⟩
    have hrem := taylor_remainder_bound f n a ((y * z : ℕ) : ℝ) D (Nat.cast_nonneg _) hsmall
      (fun x hx => hD x (hinterval hx))
    have hpower : (((y * z : ℕ) : ℝ)) ^ (n + 1) ≤ (M : ℝ) ^ (2 * (n + 1)) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hyz _
    have hrem' : |f ((a + y * z : ℕ) : ℝ) -
        (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
          iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))| ≤
        D * (M : ℝ) ^ (2 * (n + 1)) := by
      push_cast
      simpa only [Nat.cast_mul] using hrem.trans (mul_le_mul_of_nonneg_left hpower hD0)
    exact (eC_norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left hrem' (by positivity))
  simp_rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
          ‖eC (f ((a + y * z : ℕ) : ℝ)) -
            eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖ := by
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun y _ => norm_sum_le _ _))
    _ ≤ ∑ _y ∈ Finset.range (M + 1), ∑ _z ∈ Finset.range (M + 1),
          2 * Real.pi * (D * (M : ℝ) ^ (2 * (n + 1))) := by
          exact Finset.sum_le_sum (fun y hy => Finset.sum_le_sum (fun z hz => hterm y hy z hz))
    _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring

/-- The complete Taylor error bound of page245 display4 for the printed choice of P2.
The endpoint condition keeps the Taylor segment inside the derivative interval. -/
theorem karacuba_taylor_error (c1 : ℝ) (f : ℝ → ℝ) (n N P a M : ℕ)
    (hn : 0 < n) (hP : 0 < P)
    (hM : M = ⌊(P : ℝ) ^ (c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))))⌋₊)
    (hsm : ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧
      ContDiffOn ℝ (n + 1 : ℕ) f U)
    (hD : ∀ x ∈ Set.Icc (N : ℝ) (N + P),
      |iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℝ)| ≤
        (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))))
    (ha : N ≤ a) (haP : a + M ^ 2 ≤ N + P) :
    ‖(∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      eC (f ((a + y * z : ℕ) : ℝ))) -
      ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
          iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖ ≤
      2 * Real.pi * ((M : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
  have hb := taylor_double_sum_bound f n N P a M
    ((P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ)))) hsm hD ha haP
  have hscale : (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) *
      (M : ℝ) ^ (2 * (n + 1)) ≤ (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    rw [hM]
    exact taylor_scale_bound c1 n P hn hP
  exact hb.trans (mul_le_mul_of_nonneg_left hscale (by positivity))



/-- Distinct positive derivative orders have sum at least one quarter of the square of their count. Source page245 before display5. -/
theorem card_sq_le_four_sum (T : Finset ℕ) (hpos : ∀ s ∈ T, 1 ≤ s) :
    T.card ^ 2 ≤ 4 * ∑ s ∈ T, s := by
  let m := T.card / 2
  let lo := T.filter (fun s => s ≤ m)
  let hi := T.filter (fun s => ¬ s ≤ m)
  have hlo : lo.card ≤ m := by
    have hsub : lo ⊆ Finset.Icc 1 m := by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      exact Finset.mem_Icc.mpr ⟨hpos s hs'.1, hs'.2⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hcard : lo.card + hi.card = T.card := Finset.card_filter_add_card_filter_not (s := T) (fun s => s ≤ m)
  have hhi : hi.card * (m + 1) ≤ ∑ s ∈ hi, s := by
    calc _ = ∑ _s ∈ hi, (m + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun s hs => by have := (Finset.mem_filter.mp hs).2; omega)
  have hsum : ∑ s ∈ hi, s ≤ ∑ s ∈ T, s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hr : T.card = 2 * m ∨ T.card = 2 * m + 1 := by omega
  rcases hr with hr | hr <;> nlinarith

/-- The derivative order sum is at least c0 squared times n squared over four. Source page245 before display5. -/
theorem derivative_order_sum_lower (c0 : ℝ) (n : ℕ) (T : Finset ℕ)
    (hc0 : 0 ≤ c0) (hT : T ⊆ Finset.Icc 2 n) (hcard : c0 * n ≤ T.card) :
    c0 ^ 2 * (n : ℝ) ^ 2 / 4 ≤ ∑ s ∈ T, (s : ℝ) := by
  have hnat := card_sq_le_four_sum T (fun s hs => by have := (Finset.mem_Icc.mp (hT hs)).1; omega)
  have hreal : (T.card : ℝ) ^ 2 ≤ 4 * ∑ s ∈ T, (s : ℝ) := by
    have hc : ((T.card ^ 2 : ℕ) : ℝ) ≤ ((4 * ∑ s ∈ T, s : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hc
    exact hc
  have hsquare : (c0 * n) ^ 2 ≤ (T.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcard 2
  nlinarith



/-- A positive quantity below A lies between consecutive decreasing powers times A. Source page245 choice of l before display5. -/
theorem geometric_cutoff (A R y : ℝ) (hA : 0 < A) (hR : 0 < R) (hRA : R < A)
    (hy0 : 0 < y) (hy1 : y < 1) :
    ∃ l : ℕ, 0 < l ∧ A * y ^ l ≤ R ∧ R < A * y ^ (l - 1) := by
  have hex : ∃ l : ℕ, y ^ l ≤ R / A := by
    obtain ⟨l, hl⟩ := exists_pow_lt_of_lt_one (div_pos hR hA) hy1
    exact ⟨l, hl.le⟩
  let l := Nat.find hex
  have hl := Nat.find_spec hex
  have hlpos : 0 < l := by
    by_contra h
    have hl0 : l = 0 := by omega
    change y ^ l ≤ R / A at hl
    rw [hl0, pow_zero, le_div_iff₀ hA] at hl
    nlinarith
  have hprev : ¬ y ^ (l - 1) ≤ R / A := Nat.find_min hex (by omega : l - 1 < l)
  refine ⟨l, hlpos, ?_, ?_⟩
  · simpa [mul_comm] using (le_div_iff₀ hA).mp hl
  · simpa [mul_comm] using (div_lt_iff₀ hA).mp (lt_of_not_ge hprev)
/-- The geometric cutoff is bounded by the logarithmic constant times n. Source page245 choice of l before display5. -/
theorem cutoff_log_bound (n l : ℕ) (η x : ℝ) (hn : 2 ≤ n) (hl : 0 < l)
    (hη0 : 0 < η) (hηlog : Real.log η ≤ -1) (hη : η ≤ x)
    (hprev : x < (1 - 1 / (n : ℝ)) ^ (l - 1)) :
    (l : ℝ) < (-2 * Real.log η) * n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr1 : (1 : ℝ) < n := by linarith
  have hy0 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hnr]
    exact hnr1
  have hlog := Real.log_lt_log hη0 (hη.trans_lt hprev)
  rw [Real.log_pow] at hlog
  have hylog : Real.log (1 - 1 / (n : ℝ)) ≤ -(1 / (n : ℝ)) := by
    have := Real.log_le_sub_one_of_pos hy0
    linarith
  have hupper := mul_le_mul_of_nonneg_left hylog (Nat.cast_nonneg (α := ℝ) (l - 1))
  have hdiv : Real.log η < -((l - 1 : ℕ) : ℝ) / (n : ℝ) := by
    calc Real.log η < ((l - 1 : ℕ) : ℝ) * Real.log (1 - 1 / (n : ℝ)) := hlog
      _ ≤ ((l - 1 : ℕ) : ℝ) * -(1 / (n : ℝ)) := hupper
      _ = _ := by ring
  have hmul := (lt_div_iff₀ hnr).mp hdiv
  have hsub : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hsub] at hmul
  have hlogn := mul_le_mul_of_nonneg_right hηlog hnr.le
  nlinarith

/-- The choice of l in the large n proof, with the paper constant c5.
Source page245 before display5 and page248 after display8. -/
theorem karacuba_cutoff (c0 ρ : ℝ) (n : ℕ) (T : Finset ℕ)
    (hc0 : 0 < c0) (hc01 : c0 < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hn : 2 ≤ n) (hT : T ⊆ Finset.Icc 2 n) (hcard : c0 * n ≤ T.card) :
    ∃ l : ℕ, 0 < l ∧
      (n : ℝ) * (n + 1) * (1 - 1 / (n : ℝ)) ^ l ≤ ρ * ∑ s ∈ T, (s : ℝ) ∧
      ρ * (∑ s ∈ T, (s : ℝ)) < (n : ℝ) * (n + 1) * (1 - 1 / (n : ℝ)) ^ (l - 1) ∧
      (l : ℝ) < (-2 * Real.log (ρ * c0 ^ 2 / 8)) * n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by linarith
  have hA : (0 : ℝ) < (n : ℝ) * (n + 1) := by positivity
  have hsL := derivative_order_sum_lower c0 n T hc0.le hT hcard
  have hspos : (0 : ℝ) < ∑ s ∈ T, (s : ℝ) := lt_of_lt_of_le (by positivity) hsL
  have hcardNat : T.card ≤ n := by
    have h := Finset.card_le_card hT
    rw [Nat.card_Icc] at h
    omega
  have hcardr : (T.card : ℝ) ≤ n := by exact_mod_cast hcardNat
  have hsU : ∑ s ∈ T, (s : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc _ ≤ ∑ _s ∈ T, (n : ℝ) := Finset.sum_le_sum (fun s hs => by
            exact_mod_cast (Finset.mem_Icc.mp (hT hs)).2)
      _ = (T.card : ℝ) * n := by simp
      _ ≤ (n : ℝ) ^ 2 := by nlinarith
  have hRA : ρ * (∑ s ∈ T, (s : ℝ)) < (n : ℝ) * (n + 1) := by
    have hscale := mul_lt_mul_of_pos_right hρ1 hspos
    nlinarith
  have hy0 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hnr]
    linarith
  have hy1 : 1 - 1 / (n : ℝ) < (1 : ℝ) := by
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  obtain ⟨l, hl, hlo, hhi⟩ := geometric_cutoff ((n : ℝ) * (n + 1))
    (ρ * ∑ s ∈ T, (s : ℝ)) (1 - 1 / (n : ℝ)) hA (mul_pos hρ hspos) hRA hy0 hy1
  refine ⟨l, hl, hlo, hhi, ?_⟩
  let η : ℝ := ρ * c0 ^ 2 / 8
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hη8 : η ≤ 1 / 8 := by dsimp [η]; nlinarith [sq_pos_of_pos hc0]
  have hηlog : Real.log η ≤ -1 := by
    have hlog := Real.log_le_log hη0 hη8
    have h8 : Real.log ((1 : ℝ) / 8) = -3 * Real.log 2 := by
      rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h8] at hlog
    linarith [Real.log_two_gt_d9]
  have hηratio : η ≤ (ρ * ∑ s ∈ T, (s : ℝ)) / ((n : ℝ) * (n + 1)) := by
    apply (le_div_iff₀ hA).mpr
    have hfactor : (n : ℝ) * (n + 1) ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
    calc η * ((n : ℝ) * (n + 1)) ≤ η * (2 * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hfactor hη0.le
      _ = ρ * (c0 ^ 2 * (n : ℝ) ^ 2 / 4) := by dsimp [η]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsL hρ.le
  have hprev : (ρ * ∑ s ∈ T, (s : ℝ)) / ((n : ℝ) * (n + 1)) <
      (1 - 1 / (n : ℝ)) ^ (l - 1) := by
    apply (div_lt_iff₀ hA).mpr
    simpa only [mul_comm] using hhi
  exact cutoff_log_bound n l η _ hn hl hη0 hηlog hηratio hprev



/-- The degree k chosen in page245 satisfies the bounds used on page248 after display8. -/
theorem moment_degree_bounds (n l : ℕ) (C : ℝ) (hn : 2 ≤ n) (hl : 0 < l)
    (hlC : (l : ℝ) < C * n) :
    let k := n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊
    ((n * (n + 1) : ℕ) : ℝ) / 4 < (k : ℝ) ∧ (k : ℝ) < (C + 1) * (n : ℝ) ^ 2 := by
  let A : ℝ := (n : ℝ) * (n + 1)
  have hA0 : 0 ≤ A / 4 + 1 := by dsimp [A]; positivity
  have hlo := Nat.lt_floor_add_one (A / 4 + 1)
  have hhi := Nat.floor_le hA0
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by linarith
  have hnl : (n : ℝ) * l < C * (n : ℝ) ^ 2 := by
    have := mul_lt_mul_of_pos_left hlC hnr
    nlinarith
  have haux : A / 4 + 1 ≤ (n : ℝ) ^ 2 := by
    dsimp [A]
    push_cast
    nlinarith
  dsimp only
  push_cast
  constructor
  · change A / 4 < (n : ℝ) * l + (⌊A / 4 + 1⌋₊ : ℝ)
    have hnl0 : (0 : ℝ) ≤ (n : ℝ) * l := by positivity
    linarith
  · change (n : ℝ) * l + (⌊A / 4 + 1⌋₊ : ℝ) < (C + 1) * (n : ℝ) ^ 2
    nlinarith



/-- The order sum and k bound give the uniform n squared exponent scale. Source page248 after display8. -/
theorem karacuba_exponent_lower (ρ c0 C S : ℝ) (n k : ℕ)
    (hρ : 0 < ρ) (hc0 : 0 < c0) (hC : 0 < C) (hn : 0 < n) (hk : 0 < k)
    (hS : c0 ^ 2 * (n : ℝ) ^ 2 / 4 ≤ S) (hK : (k : ℝ) ≤ C * (n : ℝ) ^ 2) :
    ρ * c0 ^ 2 / (32 * C ^ 2 * (n : ℝ) ^ 2) ≤ ρ * S / (8 * (k : ℝ) ^ 2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ c0 ^ 2 * (n : ℝ) ^ 2 / 4).trans hS
  have hsq : (k : ℝ) ^ 2 ≤ (C * (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hkr.le hK 2
  calc ρ * c0 ^ 2 / (32 * C ^ 2 * (n : ℝ) ^ 2) =
        ρ * (c0 ^ 2 * (n : ℝ) ^ 2 / 4) / (8 * (C * (n : ℝ) ^ 2) ^ 2) := by
          field_simp
          <;> ring
    _ ≤ ρ * S / (8 * (C * (n : ℝ) ^ 2) ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hρ.le) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hρ.le hS0) (by positivity) (by nlinarith)

/-- The two point grid bound with the cap U at integer phases. Source page244 Lemma3 and page246 display6. -/
theorem regularized_sum_of_cell_count {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (U : ℝ) (q : ℕ) (hU : 0 < U) (hq : 2 ≤ q)
    (hcount : ∀ j : ℕ, (s.filter (fun x => ⌊(q : ℝ) * Int.fract (f x)⌋₊ = j)).card ≤ 2) :
    ∑ x ∈ s, (if Int.fract (f x) = 0 then U else
      min U (1 / min (Int.fract (f x)) (1 - Int.fract (f x)))) ≤
        6 * (U + q * Real.log q) := by
  classical
  have hpoint : ∀ x, (if Int.fract (f x) = 0 then U else
      min U (1 / min (Int.fract (f x)) (1 - Int.fract (f x)))) =
      min U (1 / min (Int.fract (f x)) (1 - Int.fract (f x))) +
        (if Int.fract (f x) = 0 then U else 0) := by
    intro x
    by_cases hz : Int.fract (f x) = 0 <;> simp [hz, min_eq_right hU.le]
  have hzeroCard : (s.filter (fun x => Int.fract (f x) = 0)).card ≤ 2 := by
    apply (Finset.card_le_card ?_).trans (hcount 0)
    intro x hx
    obtain ⟨hx, hz⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx, by simp [hz]⟩
  have hzeroSum : ∑ x ∈ s, (if Int.fract (f x) = 0 then U else 0) ≤ 2 * U := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hzeroCard) hU.le
  have hsharp := capped_sum_of_cell_count_sharp s f U q hU hq hcount
  have htail := mul_le_mul_of_nonneg_left (harmonic_tail_le_log q hq)
    (by positivity : (0 : ℝ) ≤ 4 * q)
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  nlinarith

/-- One rational phase block with the paper value U at integer phases. Source page244 Lemma3 and page246 display6. -/
theorem rational_block_regularized (U : ℝ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.range q,
      (if Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β) = 0 then U else
        min U (1 / min (Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β))
          (1 - Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β)))) ≤
          6 * (U + q * Real.log q) := by
  apply regularized_sum_of_cell_count (Finset.range q)
    (fun x : ℕ => (a / q + θ / (q : ℝ) ^ 2) * x + β) U q hU hq
  intro j
  apply (Finset.card_le_card ?_).trans
    (rational_cell_card_le_two a q θ β (by omega) hgcd hθ (j : ℤ))
  intro x hx
  obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hx, ?_⟩
  rw [← Int.natCast_floor_eq_floor (by positivity), heq]

/-- Lean division by zero cannot supply the geometric sum bound at an integer phase. This is a convention check for page246 before display6. -/
theorem geometric_bound_needs_zero_convention :
    ¬ ‖∑ x ∈ Finset.range 1, eC ((0 : ℝ) * x)‖ ≤
      min (1 : ℝ) (1 / min (Int.fract (0 : ℝ)) (1 - Int.fract (0 : ℝ))) := by
  simp [eC]
/-- Page244 Lemma3 with the paper cap U at zero nearest integer distance. This is the form used on page246 in display6. -/
theorem karacuba_lemma3_regularized (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 1 ≤ q) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.Icc 1 P,
      (if Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β) = 0 then U else
        min U (1 / min (Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β))
          (1 - Int.fract ((a / q + θ / (q : ℝ) ^ 2) * x + β)))) ≤
          6 * (U + q * Real.log q) * ((P : ℝ) / q + 1) := by
  by_cases hq1 : q = 1
  · subst q
    simp only [Nat.cast_one, div_one, one_pow, Real.log_one, mul_zero, add_zero]
    calc _ ≤ ∑ _x ∈ Finset.Icc 1 P, U := by
            apply Finset.sum_le_sum
            intro x hx
            split_ifs
            · exact le_rfl
            · exact min_le_left _ _
      _ = (P : ℝ) * U := by simp
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have hq2 : 2 ≤ q := by omega
  let α : ℝ := a / q + θ / (q : ℝ) ^ 2
  let f : ℕ → ℝ := fun x => if Int.fract (α * (x + 1) + β) = 0 then U else
    min U (1 / min (Int.fract (α * (x + 1) + β)) (1 - Int.fract (α * (x + 1) + β)))
  let C : ℝ := 6 * (U + q * Real.log q)
  have hC : 0 ≤ C := by
    have hl : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    dsimp [C]
    positivity
  have hb : ∀ b : ℕ, ∑ r ∈ Finset.range q, f (q * b + r) ≤ C := by
    intro b
    have hid : ∀ r : ℕ, α * ((q * b + r : ℕ) + 1) + β =
        α * r + (β + α * ((q * b : ℕ) + 1)) := by
      intro r
      push_cast
      ring
    dsimp only [f]
    simp_rw [hid]
    exact rational_block_regularized U a q θ (β + α * ((q * b : ℕ) + 1)) hU hq2 hgcd hθ
  have hblocks : ∀ L : ℕ, ∑ x ∈ Finset.range (q * L), f x ≤ L * C := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Nat.mul_succ, Finset.sum_range_add]
      have := hb L
      push_cast
      nlinarith
  have hpad : P ≤ q * (P / q + 1) := by
    have hmod := Nat.mod_lt P (by omega : 0 < q)
    have hdiv := Nat.mod_add_div P q
    nlinarith
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    dsimp [f]
    split_ifs
    · exact hU.le
    · exact le_min hU.le (div_nonneg zero_le_one
        (le_min (Int.fract_nonneg _) (by linarith [Int.fract_lt_one (α * (x + 1) + β)])))
  have hI : ∑ x ∈ Finset.Icc 1 P,
      (if Int.fract (α * x + β) = 0 then U else
        min U (1 / min (Int.fract (α * x + β)) (1 - Int.fract (α * x + β)))) =
      ∑ x ∈ Finset.range P, f x := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, f, Nat.cast_add, Nat.cast_one]
    congr 1
    ext x
    simp only [add_comm]
  change ∑ x ∈ Finset.Icc 1 P,
      (if Int.fract (α * x + β) = 0 then U else
        min U (1 / min (Int.fract (α * x + β)) (1 - Int.fract (α * x + β)))) ≤ C * _
  rw [hI]
  calc _ ≤ ∑ x ∈ Finset.range (q * (P / q + 1)), f x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hpad) (fun x _ _ => hfn x)
    _ ≤ ((P / q + 1 : ℕ) : ℝ) * C := hblocks _
    _ ≤ C * ((P : ℝ) / q + 1) := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left ?_ hC
      push_cast
      have hd : ((P / q : ℕ) : ℝ) ≤ (P : ℝ) / q := Nat.cast_div_le
      linarith







/-- A shifted finite correlation is at most its zero shift energy. Source page246 property a of Jk, after its counting interpretation. -/
theorem partial_correlation_le_energy {G : Type*} [AddGroup G] [DecidableEq G] (s : Finset G) (f : G → ℝ) (a : G) :
    ∑ x ∈ s.filter (fun x => x + a ∈ s), f x * f (x + a) ≤ ∑ x ∈ s, f x ^ 2 := by
  classical
  let t := s.filter (fun x => x + a ∈ s)
  have hleft : ∑ x ∈ t, f x ^ 2 ≤ ∑ x ∈ s, f x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun x _ _ => sq_nonneg _)
  have hsub : t.image (fun x => x + a) ⊆ s := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  have hright : ∑ x ∈ t, f (x + a) ^ 2 ≤ ∑ x ∈ s, f x ^ 2 := by
    have hi : Set.InjOn (fun x : G => x + a) t := by
      intro x hx y hy h
      exact add_right_cancel h
    have heq : ∑ y ∈ t.image (fun x => x + a), f y ^ 2 = ∑ x ∈ t, f (x + a) ^ 2 :=
      Finset.sum_image hi
    rw [← heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => sq_nonneg _)
  have hlocal : 2 * (∑ x ∈ t, f x * f (x + a)) ≤
      (∑ x ∈ t, f x ^ 2) + ∑ x ∈ t, f (x + a) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun x _ => by nlinarith [sq_nonneg (f x - f (x + a))])
  change ∑ x ∈ t, f x * f (x + a) ≤ _
  linarith



/-- The first Holder step on the complex rows. Source page246 first inequality, before display5. Reuses Mathlib rpow_sum_le_const_mul_sum_rpow. -/
theorem first_holder_step {ι : Type*} (s : Finset ι) (f : ι → ℂ) (k : ℕ) (hk : 0 < k) :
    ‖∑ i ∈ s, f i‖ ^ (2 * k) ≤ (s.card : ℝ) ^ (2 * k - 1) *
      ∑ i ∈ s, ‖f i‖ ^ (2 * k) := by
  have hp : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k)
  have h := Real.rpow_sum_le_const_mul_sum_rpow s (fun i => ‖f i‖) hp
  have hexp : ((2 * k : ℕ) : ℝ) - 1 = ((2 * k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hexp] at h
  simp only [abs_of_nonneg (norm_nonneg _), Real.rpow_natCast] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) (2 * k)).trans h

/-- The real Fourier moment integrand need not be nonnegative. Source page246 definition of Jk. This rules out a pointwise positivity shortcut. -/
theorem moment_coefficient_integrand_sign :
    ‖(1 : ℂ) + Complex.exp (Real.pi * Complex.I) +
      Complex.exp (2 * Real.pi * Complex.I)‖ ^ 2 * Real.cos Real.pi < 0 := by
  simp



/-- The positive coefficient approximation with Q equal to the floor of its reciprocal. Source page247 before display7. -/
theorem positive_reciprocal_floor_approx (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    let q := ⌊b⁻¹⌋₊
    1 ≤ q ∧ b⁻¹ - 1 < (q : ℝ) ∧ (q : ℝ) ≤ b⁻¹ ∧
      ∃ θ : ℝ, |θ| ≤ 1 ∧ b = 1 / (q : ℝ) + θ / (q : ℝ) ^ 2 := by
  let q := ⌊b⁻¹⌋₊
  have hbInv : (1 : ℝ) ≤ b⁻¹ := (one_le_inv₀ hb).mpr hb1
  have hq1 : 1 ≤ q := (Nat.one_le_floor_iff _).mpr hbInv
  have hqr1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hle : (q : ℝ) ≤ b⁻¹ := Nat.floor_le (by positivity)
  have hlt : b⁻¹ < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbq : b * q ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hle hb.le
    simpa only [mul_inv_cancel₀ hb.ne'] using this
  have hqUpper : 1 ≤ b * ((q : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_left hlt hb
    simpa only [mul_inv_cancel₀ hb.ne'] using this.le
  refine ⟨hq1, by linarith, hle, b * (q : ℝ) ^ 2 - q, ?_, ?_⟩
  · rw [abs_le]
    have hm := mul_le_mul_of_nonneg_right hqUpper (by linarith : 0 ≤ (q : ℝ) - 1)
    have hm' := mul_le_mul_of_nonneg_right hbq hqr.le
    constructor <;> nlinarith
  · change b = 1 / (q : ℝ) + (b * (q : ℝ) ^ 2 - q) / (q : ℝ) ^ 2
    field_simp
    <;> ring

/-- The signed coefficient approximation has numerator one or minus one and coprime denominator. Source page247 before display7. -/
theorem signed_reciprocal_floor_approx (b : ℝ) (hb : b ≠ 0) (hb1 : |b| ≤ 1) :
    let q := ⌊|b|⁻¹⌋₊
    1 ≤ q ∧ |b|⁻¹ - 1 < (q : ℝ) ∧ (q : ℝ) ≤ |b|⁻¹ ∧
      ∃ (a : ℤ) (θ : ℝ), Int.gcd a q = 1 ∧ |θ| ≤ 1 ∧
        b = a / q + θ / (q : ℝ) ^ 2 := by
  obtain ⟨hq, hlo, hhi, θ, hθ, heq⟩ := positive_reciprocal_floor_approx |b| (abs_pos.mpr hb) hb1
  refine ⟨hq, hlo, hhi, ?_⟩
  rcases lt_or_gt_of_ne hb with hb | hb
  · refine ⟨-1, -θ, by simp, by simpa using hθ, ?_⟩
    rw [abs_of_neg hb] at heq
    rw [abs_of_neg hb]
    push_cast
    simp only [neg_div]
    linarith
  · refine ⟨1, θ, by simp, hθ, ?_⟩
    simpa only [Int.cast_one, abs_of_pos hb] using heq

/-- The reciprocal floor denominator is bounded using Mathlib div_two_lt_floor. Source page247 after display7. -/
theorem reciprocal_floor_inverse_bound (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    (1 : ℝ) / ⌊b⁻¹⌋₊ ≤ 2 * b := by
  have hbInv : (1 : ℝ) ≤ b⁻¹ := (one_le_inv₀ hb).mpr hb1
  have hhalf := Nat.div_two_lt_floor hbInv
  have hfloor : (0 : ℝ) < ⌊b⁻¹⌋₊ := lt_trans (by positivity) hhalf
  apply (div_le_iff₀ hfloor).mpr
  have hm := mul_lt_mul_of_pos_left hhalf hb
  have hh : b * (b⁻¹ / 2) = (1 : ℝ) / 2 := by field_simp
  rw [hh] at hm
  nlinarith
/-- The two bounds on Q from the derivative coefficient bounds. Source page247 around display7. -/
theorem coefficient_denominator_bounds (P A B b : ℝ) (hP : 0 < P) (hb : 0 < b) (hb1 : b ≤ 1)
    (hlo : P ^ (-A) ≤ b) (hhi : b ≤ P ^ (-B)) :
    (1 : ℝ) / ⌊b⁻¹⌋₊ ≤ 2 * P ^ (-B) ∧ (⌊b⁻¹⌋₊ : ℝ) ≤ P ^ A := by
  refine ⟨(reciprocal_floor_inverse_bound b hb hb1).trans (by linarith), ?_⟩
  have hi : b⁻¹ ≤ (P ^ (-A))⁻¹ := (inv_le_inv₀ hb (Real.rpow_pos_of_pos hP _)).mpr hlo
  rw [Real.rpow_neg hP.le, inv_inv] at hi
  exact (Nat.floor_le (inv_nonneg.mpr hb.le)).trans hi



open LeanLab.ExceptionalSet.U1539

/-- The geometric sum estimate used before page246 display6. Reuses the proved PNTPort Vinogradov norm_sum_Ioc_e_le. -/
theorem geometric_sum_bound (U : ℕ) (α : ℝ) :
    ‖∑ x ∈ Finset.Icc 1 U, eC (α * x)‖ ≤
      if Int.fract α = 0 then (U : ℝ) else
        min (U : ℝ) (1 / min (Int.fract α) (1 - Int.fract α)) := by
  have hset : Finset.Icc 1 U = Finset.Ioc 0 (0 + U) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have heq : ∑ x ∈ Finset.Icc 1 U, eC (α * x) =
      ∑ x ∈ Finset.Ioc 0 (0 + U), LeanLab.PNTPort.LargeSieve.e (x * α) := by
    rw [hset]
    apply Finset.sum_congr rfl
    intro x hx
    unfold eC LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  rw [heq]
  apply (LeanLab.PNTPort.Vinogradov.norm_sum_Ioc_e_le 0 U α).trans
  have hdist : LeanLab.PNTPort.LargeSieve.dist0 α = min (Int.fract α) (1 - Int.fract α) :=
    abs_sub_round_eq_min α
  by_cases hz : Int.fract α = 0
  · simp [LeanLab.PNTPort.Vinogradov.G, hdist, hz]
  · have hfpos : 0 < Int.fract α := lt_of_le_of_ne (Int.fract_nonneg α) (Ne.symm hz)
    have hdpos : 0 < min (Int.fract α) (1 - Int.fract α) :=
      lt_min hfpos (by linarith [Int.fract_lt_one α])
    simp only [LeanLab.PNTPort.Vinogradov.G, hdist, if_neg hdpos.ne', if_neg hz]
    exact min_le_min_left _ (one_div_le_one_div_of_le hdpos (by linarith))

/-- Lemma3 applied to the symmetric integer range for the sums in page246 display6 and page247 display7. -/
theorem signed_interval_reciprocal_bound (U : ℝ) (L : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 1 ≤ q) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ μ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      (if Int.fract ((a / q + θ / (q : ℝ) ^ 2) * μ + β) = 0 then U else
        min U (1 / min (Int.fract ((a / q + θ / (q : ℝ) ^ 2) * μ + β))
          (1 - Int.fract ((a / q + θ / (q : ℝ) ^ 2) * μ + β)))) ≤
      6 * (U + q * Real.log q) * (((2 * L + 1 : ℕ) : ℝ) / q + 1) := by
  let α : ℝ := a / q + θ / (q : ℝ) ^ 2
  let g : ℝ → ℝ := fun z => if Int.fract z = 0 then U else
    min U (1 / min (Int.fract z) (1 - Int.fract z))
  have heq : ∑ x ∈ Finset.Icc 1 (2 * L + 1), g (α * x + (β - α * (L + 1))) =
      ∑ μ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), g (α * μ + β) := by
    apply Finset.sum_bij (fun (x : ℕ) _ => (x : ℤ) - (L + 1))
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx y hy heq
      omega
    · intro μ hμ
      refine ⟨(μ + (L + 1)).toNat, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hμ ⊢
        omega
      · simp only [Finset.mem_Icc] at hμ
        omega
    · intro x hx
      congr 1
      push_cast
      ring
  have h := karacuba_lemma3_regularized U (2 * L + 1) a q θ
    (β - α * (L + 1)) hU hq hgcd hθ
  change ∑ μ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), g (α * μ + β) ≤ _
  rw [← heq]
  exact h



/-- The factor thirty in the reciprocal sum estimate on page247 before display7. The paper has k greater than thirty nine, so the sufficient lower bound seven applies. -/
theorem karacuba_factor_thirty (k X : ℝ) (q : ℕ) (hk : 7 ≤ k) (hX : 1 ≤ X) (hq : 1 ≤ q) :
    6 * (2 * k * X + 1 + q * Real.log q) * ((2 * k * X + 1) / q + 1) ≤
      30 * k ^ 2 * X ^ 2 * (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := by
  have hk0 : 0 ≤ k := by linarith
  have hX0 : 0 < X := by linarith
  have hL : 7 ≤ k * X := by nlinarith [mul_le_mul_of_nonneg_left hX hk0]
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  by_cases hq1 : q = 1
  · subst q
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero, div_one]
    nlinarith [sq_nonneg (k * X - 4)]
  have hq2 : 2 ≤ q := by omega
  have hlog : (2 / 3 : ℝ) ≤ Real.log q := by
    have hmono : Real.log (2 : ℝ) ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
    linarith [Real.log_two_gt_d9]
  have hlog0 : 0 ≤ Real.log q := by linarith
  let U : ℝ := 2 * k * X + 1
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hUsq : U ^ 2 ≤ 5 * (k * X) ^ 2 := by
    dsimp [U]
    nlinarith [sq_nonneg (k * X - 3)]
  have hfirst : 6 * U ^ 2 / q ≤ 30 * k ^ 2 * X ^ 2 / q := by
    apply div_le_div_of_nonneg_right ?_ hqr.le
    nlinarith [hUsq]
  have hlinear : 6 * U ≤ 9 * U * Real.log q := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 9 * U)]
  have hmid0 : 15 * U ≤ 30 * k ^ 2 * X := by
    have hmul := mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ k * X)
    dsimp [U]
    nlinarith
  have hmid : 6 * U + 6 * U * Real.log q ≤ 30 * k ^ 2 * X * Real.log q := by
    nlinarith [mul_le_mul_of_nonneg_right hmid0 hlog0]
  have hlast : 6 * q * Real.log q ≤ 30 * k ^ 2 * q * Real.log q := by
    have hbase : (6 : ℝ) ≤ 30 * k ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hbase (mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hlog0)
    nlinarith
  have hleft : 6 * (U + q * Real.log q) * (U / q + 1) =
      6 * U ^ 2 / q + (6 * U + 6 * U * Real.log q) + 6 * q * Real.log q := by
    field_simp
    <;> ring
  have hright : 30 * k ^ 2 * X ^ 2 *
      (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) =
        30 * k ^ 2 * X ^ 2 / q + 30 * k ^ 2 * X * Real.log q +
          30 * k ^ 2 * q * Real.log q := by
    field_simp
    <;> ring
  change 6 * (U + q * Real.log q) * (U / q + 1) ≤ _
  rw [hleft, hright]
  linarith



/-- The square root threshold in n0 gives c1 n squared at least one. Source page245 choice of n0 and page247 P2 estimates. -/
theorem karacuba_large_order_scale (c1 : ℝ) (n : ℕ) (hc1 : 0 < c1)
    (hn : 1 / Real.sqrt c1 ≤ n) : 1 ≤ c1 * (n : ℝ) ^ 2 := by
  have hs : 0 < Real.sqrt c1 := Real.sqrt_pos.mpr hc1
  have hm : 1 ≤ (n : ℝ) * Real.sqrt c1 := (div_le_iff₀ hs).mp hn
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm 2
  simpa only [one_pow, mul_pow, Real.sq_sqrt hc1.le, mul_comm] using hp

/-- The printed P2 is positive and has reciprocal at most twice P to minus c1 over three. Source page247 after display7. -/
theorem karacuba_shift_floor_bounds (c1 : ℝ) (n P : ℕ) (hc1 : 0 < c1) (hn : 2 ≤ n)
    (hP : 0 < P) (hscale : 1 ≤ c1 * (n : ℝ) ^ 2) :
    let M := ⌊(P : ℝ) ^ (c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))))⌋₊
    1 ≤ M ∧ (1 : ℝ) / M ≤ 2 * (P : ℝ) ^ (-(c1 / 3)) := by
  let e : ℝ := c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hd : (0 : ℝ) < 2 * ((n : ℝ) ^ 2 * (n + 1)) := by positivity
  have he : c1 / 3 ≤ e := by
    have hm := mul_le_mul_of_nonneg_right hscale (by positivity : (0 : ℝ) ≤ n + 1)
    have hi : 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) ≤ c1 / 6 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    dsimp [e]
    linarith
  have he0 : 0 ≤ e := le_trans (by positivity) he
  have hpow1 : (1 : ℝ) ≤ (P : ℝ) ^ e := Real.one_le_rpow hP1 he0
  have hb : 0 < (P : ℝ) ^ (-e) := Real.rpow_pos_of_pos hPr _
  have hb1 : (P : ℝ) ^ (-e) ≤ 1 := by
    calc _ ≤ (P : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
      _ = 1 := Real.rpow_zero _
  have hi : ((P : ℝ) ^ (-e))⁻¹ = (P : ℝ) ^ e := by
    rw [Real.rpow_neg hPr.le, inv_inv]
  have hfloor := reciprocal_floor_inverse_bound ((P : ℝ) ^ (-e)) hb hb1
  rw [hi] at hfloor
  refine ⟨(Nat.one_le_floor_iff _).mpr hpow1, ?_⟩
  apply hfloor.trans
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)

end LeanLab.ExceptionalSet.Decomp538a
