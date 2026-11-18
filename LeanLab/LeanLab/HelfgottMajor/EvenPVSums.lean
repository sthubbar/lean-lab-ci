import Mathlib

/-!
# Real sum bounds for the even case of the Polya-Vinogradov completion argument

AI wrote this Lean code. It is a helper module for
`leaf_even_fourier_truncation_bound` in `SPLIT_leaf_even_case.lean`.

It proves, by pure real analysis with no characters, three bounds on sums of
`1 / sin (π a / q)` over `0 < a < q`:

* `sum_inv_sin_head_le`: the head sum over `1 ≤ a ≤ A` with `2 A ≤ q`,
* `sum_inv_sin_le`: the full sum, by folding `a` and `q - a`,
* `sum_min_inv_sin_le`: the full sum of `min (1 / sin) (1 / (L sin ^ 2))`,
  using the Jordan inequality and a telescoping bound on `1 / d ^ 2` away from
  the two ends.

All of this is standard mathematics. Nothing here bears on the status of the
Goldbach conjecture, which is open.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123

open Real

/-- For `0 < x ≤ π / 2`, `1 / sin x ≤ 1 / x + x / 3`. -/
theorem inv_sin_le {x : ℝ} (hx : 0 < x) (hx2 : x ≤ π / 2) :
    1 / sin x ≤ 1 / x + x / 3 := by
  have hs : x - x ^ 3 / 6 ≤ sin x := Real.sin_ge_sub_cube hx.le
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hx3 : x ≤ 1.6 := by linarith
  have hsq : x ^ 2 ≤ 3 := by nlinarith
  have hfac : x - x ^ 3 / 6 = x * (1 - x ^ 2 / 6) := by ring
  have hlow : 0 < x - x ^ 3 / 6 := by
    rw [hfac]
    exact mul_pos hx (by linarith)
  have hpos : 0 < sin x := lt_of_lt_of_le hlow hs
  rw [div_le_iff₀ hpos]
  have hxne : x ≠ 0 := hx.ne'
  have h1 : (1 / x + x / 3) * (x - x ^ 3 / 6) = 1 + x ^ 2 / 6 * (1 - x ^ 2 / 3) := by
    field_simp
    try ring
  have h2 : (1 / x + x / 3) * (x - x ^ 3 / 6) ≤ (1 / x + x / 3) * sin x :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h3 : 0 ≤ x ^ 2 / 6 * (1 - x ^ 2 / 3) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- The harmonic sum over `Icc 1 A` is the rational `harmonic A`. -/
theorem sum_inv_Icc_eq_harmonic (A : ℕ) :
    ∑ a ∈ Finset.Icc 1 A, 1 / (a : ℝ) = (harmonic A : ℝ) := by
  induction A with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
    push_cast
    ring

/-- Gauss sum of the first `A` positive integers, over the reals. -/
theorem sum_cast_Icc (A : ℕ) :
    ∑ a ∈ Finset.Icc 1 A, (a : ℝ) = (A : ℝ) * (A + 1) / 2 := by
  induction A with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

theorem sum_inv_sin_head_le {q A : ℕ} (hA : 1 ≤ A) (hAq : 2 * A ≤ q) :
    ∑ a ∈ Finset.Icc 1 A, 1 / sin (π * a / q) ≤
      (q / π) * (1 + log A) + π * A * (A + 1) / (6 * q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hterm : ∀ a ∈ Finset.Icc 1 A,
      1 / sin (π * a / q) ≤ (q / π) * (1 / (a : ℝ)) + (π / (3 * q)) * a := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have ha2 : (2 : ℝ) * a ≤ q := by exact_mod_cast (show 2 * a ≤ q by omega)
    have hx0 : 0 < π * a / q := div_pos (mul_pos pi_pos ha0) hq
    have hx2 : π * a / q ≤ π / 2 := by
      rw [div_le_div_iff₀ hq two_pos]
      nlinarith [mul_le_mul_of_nonneg_left ha2 pi_pos.le]
    have h := inv_sin_le hx0 hx2
    have e : 1 / (π * a / q) + π * a / q / 3
        = (q / π) * (1 / (a : ℝ)) + (π / (3 * q)) * a := by
      rw [one_div_div]
      ring
    rw [← e]
    exact h
  have hH : ∑ a ∈ Finset.Icc 1 A, 1 / (a : ℝ) ≤ 1 + log A := by
    rw [sum_inv_Icc_eq_harmonic]
    exact harmonic_le_one_add_log A
  calc ∑ a ∈ Finset.Icc 1 A, 1 / sin (π * a / q)
      ≤ ∑ a ∈ Finset.Icc 1 A, ((q / π) * (1 / (a : ℝ)) + (π / (3 * q)) * a) :=
        Finset.sum_le_sum hterm
    _ = (q / π) * ∑ a ∈ Finset.Icc 1 A, 1 / (a : ℝ)
          + (π / (3 * q)) * ∑ a ∈ Finset.Icc 1 A, (a : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (q / π) * (1 + log A) + (π / (3 * q)) * ((A : ℝ) * (A + 1) / 2) := by
        rw [sum_cast_Icc]
        have h0 : 0 ≤ (q : ℝ) / π := div_nonneg hq.le pi_pos.le
        linarith [mul_le_mul_of_nonneg_left hH h0]
    _ = (q / π) * (1 + log A) + π * A * (A + 1) / (6 * q) := by ring

/-- Reflection `a ↦ q - a` leaves `sin (π a / q)` unchanged. -/
theorem sin_pi_reflect {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    sin (π * ((q - a : ℕ) : ℝ) / q) = sin (π * a / q) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [Nat.cast_sub ha]
  have e : π * ((q : ℝ) - a) / q = π - π * a / q := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hq']
    ring
  rw [e, Real.sin_pi_sub]

/-- `sin (π a / q)` is positive for `0 < a < q`. -/
theorem sin_pi_div_pos {q a : ℕ} (ha0 : 0 < a) (haq : a < q) :
    0 < sin (π * a / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ha : (0 : ℝ) < a := by exact_mod_cast ha0
  have haq' : (a : ℝ) < q := by exact_mod_cast haq
  apply Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos pi_pos ha) hq)
  rw [div_lt_iff₀ hq]
  exact mul_lt_mul_of_pos_left haq' pi_pos

/-- Folding: a pointwise bound by `u a + u (q - a)` gives twice the sum of `u`. -/
theorem sum_Ioo_le_two_mul (q : ℕ) (F u : ℕ → ℝ)
    (h : ∀ a ∈ Finset.Ioo 0 q, F a ≤ u a + u (q - a)) :
    ∑ a ∈ Finset.Ioo 0 q, F a ≤ 2 * ∑ a ∈ Finset.Ioo 0 q, u a := by
  have hr : ∑ a ∈ Finset.Ioo 0 q, u (q - a) = ∑ a ∈ Finset.Ioo 0 q, u a := by
    refine Finset.sum_nbij' (fun a => q - a) (fun a => q - a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Ioo] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Ioo] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Ioo] at ha
      show q - (q - a) = a
      omega
    · intro a ha
      simp only [Finset.mem_Ioo] at ha
      show q - (q - a) = a
      omega
    · intro a _
      rfl
  calc ∑ a ∈ Finset.Ioo 0 q, F a
      ≤ ∑ a ∈ Finset.Ioo 0 q, (u a + u (q - a)) := Finset.sum_le_sum h
    _ = 2 * ∑ a ∈ Finset.Ioo 0 q, u a := by
        rw [Finset.sum_add_distrib, hr]
        ring

/-- A sum over `Ioo 0 q` cut off at `a ≤ A` is the sum over `Icc 1 A`. -/
theorem sum_Ioo_ite_eq {q A : ℕ} (hAq : A < q) (g : ℕ → ℝ) :
    ∑ a ∈ Finset.Ioo 0 q, (if a ≤ A then g a else 0) = ∑ a ∈ Finset.Icc 1 A, g a := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext a
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Icc]
  omega

theorem ite_inv_sin_nonneg {q A b : ℕ} (hb0 : 0 < b) (hbq : b < q) :
    0 ≤ (if b ≤ A then 1 / sin (π * b / q) else 0) := by
  have h := sin_pi_div_pos hb0 hbq
  split_ifs
  · positivity
  · exact le_rfl

theorem inv_sin_le_ite {q A a : ℕ} (ha0 : 0 < a) (haq : a < q)
    (hcov : a ≤ A ∨ q - a ≤ A) :
    1 / sin (π * a / q) ≤
      (if a ≤ A then 1 / sin (π * a / q) else 0)
        + (if q - a ≤ A then 1 / sin (π * ((q - a : ℕ) : ℝ) / q) else 0) := by
  have n1 := ite_inv_sin_nonneg (A := A) ha0 haq
  have n2 := ite_inv_sin_nonneg (A := A) (b := q - a) (q := q) (by omega) (by omega)
  rcases hcov with h | h
  · rw [if_pos h]
    linarith
  · rw [if_pos h, sin_pi_reflect (by omega) haq.le]
    linarith

theorem sum_inv_sin_le {q : ℕ} (hq : 2 ≤ q) :
    ∑ a ∈ Finset.Ioo 0 q, 1 / sin (π * a / q) ≤
      2 * ((q / π) * (1 + log (q / 2)) + π * (q + 2) / 24) := by
  obtain ⟨A, hA1, hA2, hA3⟩ : ∃ A : ℕ, 1 ≤ A ∧ 2 * A ≤ q ∧ q ≤ 2 * A + 1 :=
    ⟨q / 2, by omega, by omega, by omega⟩
  have h1 : ∑ a ∈ Finset.Ioo 0 q, 1 / sin (π * a / q) ≤
      2 * ∑ a ∈ Finset.Ioo 0 q, (if a ≤ A then 1 / sin (π * a / q) else 0) := by
    refine sum_Ioo_le_two_mul q _
      (fun a : ℕ => if a ≤ A then 1 / sin (π * a / q) else 0) ?_
    intro a ha
    rw [Finset.mem_Ioo] at ha
    exact inv_sin_le_ite ha.1 ha.2 (by omega)
  rw [sum_Ioo_ite_eq (by omega)] at h1
  have h2 := sum_inv_sin_head_le hA1 hA2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA1
  have hA2r : (2 : ℝ) * A ≤ q := by exact_mod_cast hA2
  have hAr : (A : ℝ) ≤ q / 2 := by
    rw [le_div_iff₀ two_pos]
    linarith
  have hlog : log (A : ℝ) ≤ log (q / 2) := Real.log_le_log hA0 hAr
  have hfirst : (q / π) * (1 + log A) ≤ (q / π) * (1 + log (q / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hq0.le pi_pos.le)
  have hsecond : π * A * (A + 1) / (6 * q) ≤ π * (q + 2) / 24 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have hAA : (2 * (A : ℝ)) * (2 * A + 2) ≤ q * (q + 2) :=
      mul_le_mul hA2r (by linarith) (by linarith) hq0.le
    nlinarith [mul_le_mul_of_nonneg_left hAA pi_pos.le]
  linarith

/-- Jordan inequality applied to the second entry of the minimum. -/
theorem inv_sin_sq_le {q b L : ℕ} (hL : 1 ≤ L) (hb : 0 < b) (hbq : 2 * b ≤ q) :
    1 / (L * sin (π * b / q) ^ 2) ≤ (q : ℝ) ^ 2 / (4 * L) * (1 / (b : ℝ) ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hb2 : (2 : ℝ) * b ≤ q := by exact_mod_cast hbq
  have hx0 : 0 ≤ π * b / q := (div_pos (mul_pos pi_pos hb0) hq).le
  have hx2 : π * b / q ≤ π / 2 := by
    rw [div_le_div_iff₀ hq two_pos]
    nlinarith [mul_le_mul_of_nonneg_left hb2 pi_pos.le]
  have hJ := Real.mul_le_sin hx0 hx2
  have e : 2 / π * (π * b / q) = 2 * b / q := by
    rw [div_mul_div_comm, div_eq_div_iff (mul_pos pi_pos hq).ne' hq.ne']
    ring
  rw [e] at hJ
  have hpos : 0 < 2 * (b : ℝ) / q := div_pos (by linarith) hq
  have hsq : (2 * (b : ℝ) / q) ^ 2 ≤ sin (π * b / q) ^ 2 :=
    pow_le_pow_left₀ hpos.le hJ 2
  have hden : (L : ℝ) * (2 * b / q) ^ 2 ≤ L * sin (π * b / q) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hL0.le
  have h := one_div_le_one_div_of_le (mul_pos hL0 (pow_pos hpos 2)) hden
  have hqn : (q : ℝ) ≠ 0 := hq.ne'
  have hbn : (b : ℝ) ≠ 0 := hb0.ne'
  have hLn : (L : ℝ) ≠ 0 := hL0.ne'
  have e2 : 1 / ((L : ℝ) * (2 * b / q) ^ 2) = (q : ℝ) ^ 2 / (4 * L) * (1 / (b : ℝ) ^ 2) := by
    field_simp
    try ring
  rw [← e2]
  exact h

theorem inv_sq_step {m : ℝ} (hm : 0 < m) : 1 / (m + 1) ^ 2 ≤ 1 / m - 1 / (m + 1) := by
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  have e : 1 / m - 1 / (m + 1) = 1 / (m * (m + 1)) := by
    rw [div_sub_div _ _ hm.ne' hm1.ne']
    congr 1
    ring
  rw [e]
  exact one_div_le_one_div_of_le (mul_pos hm hm1) (by nlinarith)

/-- Telescoping bound on the tail of `∑ 1 / a ^ 2`. -/
theorem sum_inv_sq_Ioc_le {A : ℕ} (hA : 1 ≤ A) (n : ℕ) :
    ∑ a ∈ Finset.Ioc A (A + n), 1 / (a : ℝ) ^ 2 ≤ 1 / (A : ℝ) - 1 / ((A + n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : (0 : ℝ) < ((A + n : ℕ) : ℝ) := by exact_mod_cast (show 0 < A + n by omega)
    have hs := inv_sq_step hm
    have hrw : A + (n + 1) = (A + n) + 1 := by omega
    rw [hrw, Finset.sum_Ioc_succ_top (by omega), Nat.cast_add_one]
    linarith

theorem ite_sq_nonneg (q A L b : ℕ) :
    0 ≤ (if A < b ∧ 2 * b ≤ q then (q : ℝ) ^ 2 / (4 * L) * (1 / (b : ℝ) ^ 2) else 0) := by
  split_ifs
  · positivity
  · exact le_rfl

theorem inv_sin_sq_le_ite {q A L a : ℕ} (hL : 1 ≤ L) (ha0 : 0 < a) (haq : a < q)
    (h1 : A < a) (h2 : A < q - a) :
    1 / (L * sin (π * a / q) ^ 2) ≤
      (if A < a ∧ 2 * a ≤ q then (q : ℝ) ^ 2 / (4 * L) * (1 / (a : ℝ) ^ 2) else 0)
        + (if A < q - a ∧ 2 * (q - a) ≤ q then
            (q : ℝ) ^ 2 / (4 * L) * (1 / (((q - a : ℕ) : ℝ)) ^ 2) else 0) := by
  have n1 := ite_sq_nonneg q A L a
  have n2 := ite_sq_nonneg q A L (q - a)
  by_cases h : 2 * a ≤ q
  · rw [if_pos (⟨h1, h⟩ : A < a ∧ 2 * a ≤ q)]
    have := inv_sin_sq_le hL ha0 h
    linarith
  · have h' : 2 * (q - a) ≤ q := by omega
    rw [if_pos (⟨h2, h'⟩ : A < q - a ∧ 2 * (q - a) ≤ q)]
    have := inv_sin_sq_le (b := q - a) hL (by omega) h'
    rw [sin_pi_reflect (by omega) haq.le] at this
    linarith

theorem sum_ite_sq_le {q A L : ℕ} (hL : 1 ≤ L) (hA : 1 ≤ A) :
    ∑ a ∈ Finset.Ioo 0 q,
        (if A < a ∧ 2 * a ≤ q then (q : ℝ) ^ 2 / (4 * L) * (1 / (a : ℝ) ^ 2) else 0)
      ≤ (q : ℝ) ^ 2 / (4 * L * A) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  rw [← Finset.sum_filter]
  have hsub : (Finset.Ioo 0 q).filter (fun a => A < a ∧ 2 * a ≤ q)
      ⊆ Finset.Ioc A (A + q) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ioc] at ha ⊢
    omega
  calc _ ≤ ∑ a ∈ Finset.Ioc A (A + q), (q : ℝ) ^ 2 / (4 * L) * (1 / (a : ℝ) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    _ = (q : ℝ) ^ 2 / (4 * L) * ∑ a ∈ Finset.Ioc A (A + q), 1 / (a : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (q : ℝ) ^ 2 / (4 * L) * (1 / (A : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 := sum_inv_sq_Ioc_le hA q
        have h2 : (0 : ℝ) ≤ 1 / ((A + q : ℕ) : ℝ) := by positivity
        linarith
    _ = (q : ℝ) ^ 2 / (4 * L * A) := by ring

theorem sum_min_inv_sin_le {q A L : ℕ} (hL : 1 ≤ L) (hA : 1 ≤ A) (hAq : 2 * A < q) :
    ∑ a ∈ Finset.Ioo 0 q, min (1 / sin (π * a / q)) (1 / (L * sin (π * a / q) ^ 2)) ≤
      2 * ((q / π) * (1 + log A) + π * A * (A + 1) / (6 * q) + q ^ 2 / (4 * L * A)) := by
  have hA' : A < q := by omega
  have key : ∑ a ∈ Finset.Ioo 0 q,
        min (1 / sin (π * a / q)) (1 / (L * sin (π * a / q) ^ 2)) ≤
      2 * ∑ a ∈ Finset.Ioo 0 q,
        ((if a ≤ A then 1 / sin (π * a / q) else 0)
          + (if A < a ∧ 2 * a ≤ q then
              (q : ℝ) ^ 2 / (4 * L) * (1 / (a : ℝ) ^ 2) else 0)) := by
    refine sum_Ioo_le_two_mul q _
      (fun a : ℕ => (if a ≤ A then 1 / sin (π * a / q) else 0)
          + (if A < a ∧ 2 * a ≤ q then
              (q : ℝ) ^ 2 / (4 * L) * (1 / (a : ℝ) ^ 2) else 0)) ?_
    intro a ha
    rw [Finset.mem_Ioo] at ha
    have hqa : 0 < q - a ∧ q - a < q := by omega
    have n1 := ite_inv_sin_nonneg (A := A) ha.1 ha.2
    have n2 := ite_inv_sin_nonneg (A := A) hqa.1 hqa.2
    have n3 := ite_sq_nonneg q A L a
    have n4 := ite_sq_nonneg q A L (q - a)
    by_cases c1 : a ≤ A ∨ q - a ≤ A
    · have h := inv_sin_le_ite ha.1 ha.2 c1
      refine (min_le_left _ _).trans ?_
      linarith
    · have h := inv_sin_sq_le_ite hL ha.1 ha.2 (A := A) (by omega) (by omega)
      refine (min_le_right _ _).trans ?_
      linarith
  rw [Finset.sum_add_distrib, sum_Ioo_ite_eq hA'] at key
  have h2 := sum_inv_sin_head_le hA (show 2 * A ≤ q by omega)
  have h3 := sum_ite_sq_le (q := q) hL hA
  linarith

end LeanLab.HelfgottMajor.PolyaVinogradov123
