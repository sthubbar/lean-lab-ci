import Mathlib
import LeanLab.HelfgottMajor.PVOddCot1122
import LeanLab.HelfgottMajor.PVOddTrunc1122

/-!
Route burst S68, burst-20261122, tag odd-truncated, third file.
The LEAF `PVOddTrunc1122.odd_cot_bound` from the PROVED finite Polya identity
`PVOddCot1122.polya_interval_cot`, the Gauss sum norm `PV420Split1122.norm_gauss`, and one
smaller LEAF, `cot_sum_fold`: for odd χ the terms h and -h pair to cosine differences, and the
sum over ZMod q folds onto 1 ≤ h ≤ (q-1)/2. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddCotBound1122

open Real Finset

/-- e(h/q)^n + e(-h/q)^n = 2 cos(2π h n/q). PROVED. -/
private theorem std_pow_add_neg {q : ℕ} [NeZero q] (h : ZMod q) (n : ℕ) :
    ZMod.stdAddChar h ^ n + ZMod.stdAddChar (-h) ^ n =
      2 * ((Real.cos (2 * π * h.val * n / q) : ℝ) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, inv_pow, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> push_cast <;> ring

/-- cot(π(q-h)/q) = -cot(π h/q) for h ≠ 0 in ZMod q. PROVED. -/
private theorem cot_neg_val {q : ℕ} [NeZero q] {h : ZMod q} (hh : h ≠ 0) :
    Real.cot (π * (-h).val / q) = - Real.cot (π * h.val / q) := by
  have : NeZero h := ⟨hh⟩
  rw [ZMod.val_neg_of_ne_zero]
  have hle : h.val ≤ q := (ZMod.val_lt h).le
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [Nat.cast_sub hle]
  rw [show π * ((q : ℝ) - h.val) / q = π - π * h.val / q by field_simp]
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

/-- Frolenkov display 14 step, the pairing of h with -h for odd χ in the cotangent form of the
Polya identity: the two terms add to twice χ⁻¹(h) cot(π h/q) (cos hβ - cos hα). PROVED. -/
private theorem pair_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1)
    (hm : χ⁻¹ (-1) = -1) (M N : ℕ) (h : ZMod q) :
    (χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)) +
    (χ⁻¹ (-h) * (Real.cot (π * (-h).val / q) : ℂ) *
        (ZMod.stdAddChar (-h) ^ (N + 1) - ZMod.stdAddChar (-h) ^ M)) =
      2 * (χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ))) := by
  by_cases hh : h = 0
  · subst hh; simp [DirichletCharacter.map_zero' _ hq]
  · have e1 : χ⁻¹ (-h) = -χ⁻¹ h := by
      rw [show -h = (-1) * h by ring, map_mul, hm]; ring
    rw [e1, cot_neg_val hh, Complex.ofReal_neg]
    have a := std_pow_add_neg h (N + 1)
    have b := std_pow_add_neg h M
    linear_combination (χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ)) * (a - b)


/-- The cotangent sum of the Polya identity for odd χ equals its cosine form. PROVED. -/
private theorem sum_pair {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1)
    (hm : χ⁻¹ (-1) = -1) (M N : ℕ) :
    ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) =
      ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ)) := by
  set f : ZMod q → ℂ := fun h => χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) with hf
  have hneg : ∑ h : ZMod q, f (-h) = ∑ h : ZMod q, f h := Equiv.sum_comp (Equiv.neg (ZMod q)) f
  have h2 : (2 : ℂ) * ∑ h : ZMod q, f h = 2 * ∑ h : ZMod q, χ⁻¹ h *
      (Real.cot (π * h.val / q) : ℂ) * (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ)) := by
    calc (2 : ℂ) * ∑ h : ZMod q, f h = ∑ h : ZMod q, f h + ∑ h : ZMod q, f (-h) := by
          rw [hneg]; ring
      _ = ∑ h : ZMod q, (f h + f (-h)) := Finset.sum_add_distrib.symm
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun h _ => pair_term χ hq hm M N h
  exact mul_left_cancel₀ two_ne_zero h2

/-- Norm bound of the cosine form, |χ⁻¹| ≤ 1. PROVED. -/
private theorem norm_cos_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (M N : ℕ) :
    ‖∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ))‖ ≤
      ∑ h : ZMod q, |Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  rw [norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have := DirichletCharacter.norm_le_one χ⁻¹ h
  have h0 : 0 ≤ |Real.cot (π * h.val / q)| *
      |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)| := by
    positivity
  calc ‖χ⁻¹ h‖ * |Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|
      = ‖χ⁻¹ h‖ * (|Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|) := by ring
    _ ≤ 1 * (|Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|) := by
        gcongr
    _ = _ := one_mul _


/-- The summand |cot(π v/q)| |cos(2π v (N+1)/q) - cos(2π v M/q)| is symmetric under
v ↦ q - v. PROVED. -/
private theorem G_reflect {q : ℕ} (hq : 0 < q) (M N v : ℕ) (hv : v ≤ q) :
    |Real.cot (π * ((q - v : ℕ) : ℝ) / q)| *
        |Real.cos (2 * π * ((q - v : ℕ) : ℝ) * (N + 1 : ℕ) / q) -
          Real.cos (2 * π * ((q - v : ℕ) : ℝ) * M / q)| =
      |Real.cot (π * (v : ℝ) / q)| *
        |Real.cos (2 * π * (v : ℝ) * (N + 1 : ℕ) / q) - Real.cos (2 * π * (v : ℝ) * M / q)| := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Nat.cast_sub hv]
  have e1 : π * ((q : ℝ) - v) / q = π - π * v / q := by field_simp
  have e2 : ∀ n : ℕ, 2 * π * ((q : ℝ) - v) * n / q = n * (2 * π) - 2 * π * v * n / q := by
    intro n; field_simp
  rw [e1, e2, e2, Real.cos_nat_mul_two_pi_sub, Real.cos_nat_mul_two_pi_sub,
    Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div,
    abs_neg]

/-- A sum over ZMod q of a function of the least residue is the sum over range q. PROVED. -/
private theorem sum_zmod_val {q : ℕ} [NeZero q] (G : ℕ → ℝ) :
    ∑ h : ZMod q, G h.val = ∑ v ∈ range q, G v := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := NeZero.ne q; omega⟩
  exact Fin.sum_univ_eq_sum_range G (k + 1)


/-- Folding a sum over range q of a function vanishing at 0 and at q/2, symmetric under
v ↦ q - v, onto 1 ≤ v ≤ (q-1)/2 with factor 2. PROVED. -/
private theorem fold_range {q : ℕ} (hq7 : 7 ≤ q) (G : ℕ → ℝ) (h0 : G 0 = 0)
    (hrefl : ∀ v ≤ q, G (q - v) = G v) (hhalf : 2 ∣ q → G (q / 2) = 0) :
    ∑ v ∈ range q, G v = 2 * ∑ v ∈ Icc 1 ((q - 1) / 2), G v := by
  set K := (q - 1) / 2 with hK
  have hKq : K + 1 ≤ q := by omega
  rw [← Finset.sum_range_add_sum_Ico G hKq]
  have hA : ∑ v ∈ range (K + 1), G v = ∑ v ∈ Icc 1 K, G v := by
    rw [Finset.sum_range_succ', h0, add_zero]
    have : Icc 1 K = Ico 1 (K + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun v _ => by rw [add_comm]
  have hB : ∑ v ∈ Ico (K + 1) q, G v = ∑ v ∈ Icc 1 (q - K - 1), G v := by
    refine Finset.sum_nbij' (fun v => q - v) (fun w => q - w) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Ico, mem_Icc, coe_Ico, coe_Icc, Set.mem_Ico, Set.mem_Icc] at ha ⊢
      omega
    · intro a ha; simp only [mem_Ico, mem_Icc, coe_Ico, coe_Icc, Set.mem_Ico, Set.mem_Icc] at ha ⊢
      omega
    · intro a ha; simp only [mem_Ico, coe_Ico, Set.mem_Ico] at ha; omega
    · intro a ha; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at ha; omega
    · intro a ha; simp only [mem_Ico, coe_Ico, Set.mem_Ico] at ha
      exact (hrefl a ha.2.le).symm
  rw [hA, hB]
  rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
  · have e : q - K - 1 = K + 1 := by omega
    rw [e, Finset.sum_Icc_succ_top (by omega)]
    have : K + 1 = q / 2 := by omega
    rw [this, hhalf ⟨r, by omega⟩]
    ring
  · have e : q - K - 1 = K := by omega
    rw [e]; ring



/-- LEAF: Pomerance 2011 proof of Theorem 1 for odd χ, Frolenkov display 14 step: in the
cotangent form of the Polya identity, for odd χ the terms h and -h pair, since χ⁻¹(-h) = -χ⁻¹(h)
and cot(π(q-h)/q) = -cot(π h/q), so the sum equals the sum of χ⁻¹(h) cot(π h/q) times
2(cos hβ - cos hα)/2; its norm is at most the sum over h ≠ 0 of |cot(π h/q)| |cos hα - cos hβ|,
which folds onto 1 ≤ h ≤ (q-1)/2 with factor 2, the term h = q/2 for even q being 0.
Screened with Python for odd primitive χ, 7 ≤ q < 60, M < q, N < q + 3: no violation, slack 0 up
to rounding. Class EASY. -/
theorem cot_sum_fold {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ ≤
      2 * ∑ m ∈ Icc 1 ((q - 1) / 2),
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  have hq0 : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hm1 : χ (-1) = -1 := by
    have h1 : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hodd
    · linear_combination h
  have hm : χ⁻¹ (-1) = -1 := by
    rw [MulChar.inv_apply_eq_inv', hm1]; norm_num
  rw [sum_pair χ (by omega) hm M N]
  refine (norm_cos_sum χ M N).trans ?_
  set G : ℕ → ℝ := fun v => |Real.cot (π * (v : ℝ) / q)| *
    |Real.cos (2 * π * (v : ℝ) * (N + 1 : ℕ) / q) - Real.cos (2 * π * (v : ℝ) * M / q)| with hG
  have hsum := sum_zmod_val (q := q) G
  simp only [hG] at hsum
  rw [hsum]
  have h0 : G 0 = 0 := by
    simp only [hG, Nat.cast_zero, mul_zero, zero_div, Real.cot_eq_cos_div_sin, Real.sin_zero,
      div_zero, abs_zero, zero_mul]
  have hrefl : ∀ v ≤ q, G (q - v) = G v := fun v hv => G_reflect hq0 M N v hv
  have hhalf : 2 ∣ q → G (q / 2) = 0 := by
    intro h2
    have e : π * (((q / 2 : ℕ) : ℝ)) / q = π / 2 := by
      rw [Nat.cast_div h2 (by norm_num)]; push_cast; field_simp
    simp only [hG, e, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div, abs_zero, zero_mul]
  have hf := fold_range hq7 G h0 hrefl hhalf
  simp only [hG] at hf
  rw [hf]
  gcongr 2 * ?_
  refine le_of_eq (Finset.sum_congr rfl fun m hm => ?_)
  rw [mem_Icc] at hm
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : (2 : ℝ) * m < q := by exact_mod_cast (show 2 * m < q by omega)
  have hx0 : 0 < π * m / q := by positivity
  have hx1 : π * m / q < π / 2 := by
    rw [div_lt_div_iff₀ hqr (by norm_num)]
    nlinarith [pi_pos]
  have hc : 0 ≤ Real.cot (π * m / q) := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hx1.le⟩)
      (Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith))
  rw [abs_of_nonneg hc, abs_sub_comm]
  congr 3 <;> push_cast <;> ring_nf



/-- The sum on the right of `odd_cot_bound` is nonnegative, cot being positive on (0, π/2).
PROVED. -/
theorem fold_nonneg {q : ℕ} (M N : ℕ) :
    0 ≤ ∑ m ∈ Icc 1 ((q - 1) / 2),
      Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  refine sum_nonneg fun m hm => mul_nonneg ?_ (abs_nonneg _)
  rw [mem_Icc] at hm
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : (2 : ℝ) * m < q := by exact_mod_cast (show 2 * m < q by omega)
  have hx0 : 0 < π * m / q := by positivity
  have hx1 : π * m / q < π / 2 := by
    rw [div_lt_div_iff₀ hq (by norm_num)]
    nlinarith [pi_pos]
  rw [Real.cot_eq_cos_div_sin]
  exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hx1.le⟩)
    (Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith))

/-- Exactly `PVOddTrunc1122.odd_cot_bound`, from `PVOddCot1122.polya_interval_cot`,
|τ(χ⁻¹)| = √q, |χ| ≤ 1, and the LEAF `cot_sum_fold`. PROVED from the LEAF. -/
theorem odd_cot_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 + 1 / sqrt q * ∑ m ∈ Icc 1 ((q - 1) / 2),
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  set T := ∑ m ∈ Icc 1 ((q - 1) / 2),
    Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| with hT
  have hT0 : 0 ≤ T := fold_nonneg M N
  have hsq : 0 < sqrt (q : ℝ) := sqrt_pos.mpr (by exact_mod_cast (show 0 < q by omega))
  by_cases hMN : M ≤ N + 1
  · have hid := LeanLab.HelfgottMajor.PVOddCot1122.polya_interval_cot hχ (by omega) hMN
    have hτ := LeanLab.HelfgottMajor.PV420Split1122.norm_gauss
      (LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ)
    have hF := cot_sum_fold χ hq7 hodd M N
    set τ := gaussSum χ⁻¹ ZMod.stdAddChar
    set S := ∑ m ∈ Icc M N, χ (m : ZMod q)
    set F := ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)
    have h1 : ‖χ ((N + 1 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h2 : ‖χ (M : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have hn : ‖τ * S‖ ≤ ‖τ‖ + 1 / 2 * ‖F‖ := by
      rw [hid]
      calc ‖-(1 / 2) * τ * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q)) - Complex.I / 2 * F‖
          ≤ ‖-(1 / 2) * τ * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q))‖ +
            ‖Complex.I / 2 * F‖ := norm_sub_le _ _
        _ ≤ 1 / 2 * ‖τ‖ * (‖χ ((N + 1 : ℕ) : ZMod q)‖ + ‖χ (M : ZMod q)‖) + 1 / 2 * ‖F‖ := by
          gcongr
          · rw [norm_mul, norm_mul, norm_neg]
            gcongr
            · simp
            · exact norm_sub_le _ _
          · rw [norm_mul, norm_div, Complex.norm_I]; simp
        _ ≤ ‖τ‖ + 1 / 2 * ‖F‖ := by nlinarith [norm_nonneg τ]
    rw [norm_mul, hτ] at hn
    have : sqrt q * ‖S‖ ≤ sqrt q * (1 + 1 / sqrt q * T) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_one_div_cancel hsq.ne', one_mul]
      linarith
    exact le_of_mul_le_mul_left this hsq
  · have he : Icc M N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he, sum_empty, norm_zero]
    have : 0 ≤ 1 / sqrt (q : ℝ) * T := mul_nonneg (by positivity) hT0
    linarith

example : type_of% @odd_cot_bound =
    type_of% @LeanLab.HelfgottMajor.PVOddTrunc1122.odd_cot_bound := rfl

end LeanLab.HelfgottMajor.PVOddCotBound1122

#print axioms LeanLab.HelfgottMajor.PVOddCotBound1122.cot_sum_fold
#print axioms LeanLab.HelfgottMajor.PVOddCotBound1122.fold_nonneg
#print axioms LeanLab.HelfgottMajor.PVOddCotBound1122.odd_cot_bound
