import Mathlib
import LeanLab.HelfgottMajor.PVCases1122
import LeanLab.HelfgottMajor.PVOddCot1122

/-!
Route burst S68, burst-20261122, tag odd-truncated.
Split of the LEAF `PVCases1122.odd_truncated`, Pomerance 2011 Theorem 1, odd case, in the form
of Frolenkov arXiv 1107.0381 displays 12 to 22.

The finite Polya identity, Frolenkov display 12 with display 13, written with
1/(e(h/q) - 1) = -1/2 - (i/2) cot(π h/q), pairs h with q - h for odd χ and gives the exact
interval sum as -(χ(N+1) - χ(M))/2 plus a cotangent sum over h ≤ (q-1)/2. Taking norms and
|τ(χ)| = √q gives the LEAF `odd_cot_bound`. The elementary bound cot x < 1/x on (0, π/2),
here `cot_le`, PROVED, turns it into `odd_full_bound`, PROVED from the LEAF, with the full
length H = (q-1)/2. Numerically, the remainder E(H) of `odd_truncated` at H = (q-1)/2 is at
least 1 for 7 ≤ q ≤ 14762 and below 1 from q = 14763 on, so the full length expansion closes
the LEAF for q ≤ 1000 with the PROVED arithmetic `remainder_ge_one`, and the genuine Pomerance
truncation with cancellation in the h sum is needed only for q > 1000, the LEAF
`odd_truncated_large`. The assembly `odd_truncated` has exactly the statement of
`PVCases1122.odd_truncated`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddTrunc1122

open Real Finset

/-- Frolenkov display 14 ingredient, the elementary bound cot x < 1/x for 0 < x < π/2, at
x = π h/q with 1 ≤ h and 2h < q. PROVED. -/
theorem cot_le {q h : ℕ} (hh : 1 ≤ h) (h2 : 2 * h < q) :
    Real.cot (π * h / q) ≤ q / (π * h) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h2r : (2 : ℝ) * h < q := by exact_mod_cast h2
  have hx0 : 0 < π * h / q := by positivity
  have hx1 : π * h / q < π / 2 := by
    rw [div_lt_div_iff₀ hq (by norm_num)]
    nlinarith [pi_pos]
  have ht := Real.lt_tan hx0 hx1
  have htpos : 0 < tan (π * h / q) := lt_trans hx0 ht
  have hc : Real.cot (π * h / q) = 1 / tan (π * h / q) := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, one_div_div]
  rw [hc]
  calc 1 / tan (π * h / q) ≤ 1 / (π * h / q) := one_div_le_one_div_of_le hx0 ht.le
    _ = q / (π * h) := by rw [one_div_div]

/-! Private helpers for `odd_cot_bound`: the pairing h ↦ -h in the cotangent form of the Polya
identity, and the folding of the sum over `ZMod q` onto `1 ≤ h ≤ (q-1)/2`. -/

/-- `e(h/q)^n + e(-h/q)^n = 2 cos(2π h n/q)`. -/
private theorem std_pow_add_neg {q : ℕ} [NeZero q] (h : ZMod q) (n : ℕ) :
    ZMod.stdAddChar h ^ n + ZMod.stdAddChar (-h) ^ n =
      2 * ((Real.cos (2 * π * h.val * n / q) : ℝ) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, inv_pow, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> push_cast <;> ring

/-- `cot(π(q-h)/q) = -cot(π h/q)` for `h ≠ 0` in `ZMod q`. -/
private theorem cot_neg_val {q : ℕ} [NeZero q] {h : ZMod q} (hh : h ≠ 0) :
    Real.cot (π * (-h).val / q) = - Real.cot (π * h.val / q) := by
  have : NeZero h := ⟨hh⟩
  rw [ZMod.val_neg_of_ne_zero]
  have hle : h.val ≤ q := (ZMod.val_lt h).le
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [Nat.cast_sub hle]
  rw [show π * ((q : ℝ) - h.val) / q = π - π * h.val / q by field_simp]
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

/-- Frolenkov display 14 step, the pairing of `h` with `-h` for odd χ in the cotangent form of the
Polya identity: the two terms add to twice `χ⁻¹(h) cot(π h/q) (cos hβ - cos hα)`. -/
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

/-- The cotangent sum of the Polya identity for odd χ equals its cosine form. -/
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

/-- Norm bound of the cosine form, `|χ⁻¹| ≤ 1`. -/
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

/-- The summand `|cot(π v/q)| |cos(2π v (N+1)/q) - cos(2π v M/q)|` is symmetric under
`v ↦ q - v`. -/
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

/-- A sum over `ZMod q` of a function of the least residue is the sum over `range q`. -/
private theorem sum_zmod_val {q : ℕ} [NeZero q] (G : ℕ → ℝ) :
    ∑ h : ZMod q, G h.val = ∑ v ∈ range q, G v := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := NeZero.ne q; omega⟩
  exact Fin.sum_univ_eq_sum_range G (k + 1)

/-- Folding a sum over `range q` of a function vanishing at 0 and at `q/2`, symmetric under
`v ↦ q - v`, onto `1 ≤ v ≤ (q-1)/2` with factor 2. -/
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

/-- The fold of `cot_sum_fold`: pairing of `h` with `-h` and folding onto `1 ≤ h ≤ (q-1)/2`. -/
private theorem cot_sum_fold {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
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


/-- The sum on the right of `odd_cot_bound` is nonnegative, `cot` being positive on `(0, π/2)`. -/
private theorem fold_nonneg {q : ℕ} [NeZero q] (M N : ℕ) :
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

/-- LEAF: Pomerance 2011 proof of Theorem 1 for odd χ, Frolenkov displays 12, 13 and 14 without
truncation: the finite Polya identity for the interval sum through the Gauss sum of χ⁻¹ and the
geometric inner sum, with 1/(e(h/q) - 1) = -1/2 - (i/2) cot(π h/q); the constant part gives
-(χ(N+1) - χ(M))/2 of norm at most 1, and for odd χ the terms h and q - h pair to
χ⁻¹(h) cot(π h/q) (cos hβ - cos hα), so with |τ(χ⁻¹)| = √q the interval sum is at most
1 + q^(-1/2) times the sum over 1 ≤ h ≤ (q-1)/2 of cot(π h/q) |cos hα - cos hβ|, at α = 2πM/q,
β = 2π(N+1)/q. Screened with Python for all odd primitive χ, q ≤ 79 and q = 97, 120, 151, 199,
M < q, N < 2q: no violation. Class MEDIUM. -/
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

/-- The full length expansion: `odd_cot_bound` with cot(π h/q) ≤ q/(π h) from `cot_le`, the
form of Frolenkov display 22 before truncation. PROVED from the LEAF `odd_cot_bound`. -/
theorem odd_full_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 + sqrt q / π * ∑ m ∈ Icc 1 ((q - 1) / 2),
        |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m := by
  refine (odd_cot_bound χ hχ hq7 hodd M N).trans ?_
  have hsq : 0 < sqrt (q : ℝ) := sqrt_pos.mpr (by exact_mod_cast (show 0 < q by omega))
  have hqq : (q : ℝ) = sqrt q * sqrt q := (mul_self_sqrt (Nat.cast_nonneg q)).symm
  gcongr 1 + ?_
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [mem_Icc] at hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : 2 * m < q := by omega
  have hc := cot_le hm.1 h2
  set c := |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))|
  have hc0 : 0 ≤ c := abs_nonneg _
  have hmpos : (0 : ℝ) < m := by linarith
  calc 1 / sqrt q * (Real.cot (π * m / q) * c) ≤ 1 / sqrt q * (q / (π * m) * c) := by
        gcongr
    _ = sqrt q / π * (c / m) := by
        have hs2 : sqrt (q : ℝ) ^ 2 = q := sq_sqrt (Nat.cast_nonneg q)
        field_simp
        first
          | (rw [hs2])
          | (rw [← hs2]; ring)
          | (nlinarith [hs2])
          | (simp [hs2])

/-- Final arithmetic of the full length case, the core estimate: with log H + log 2 at most
log q - 1/q, log log q at least log 2 + 1 - 2/log q, γ < 2/3 and π > 3.1415, numeric lower and
upper bounds on √q, log q and 3/H make the remainder of `PVCases1122.odd_truncated` at
H = (q-1)/2 at least 1. PROVED. -/
theorem remainder_core {q : ℕ} (hq7 : 7 ≤ q) (s0 U L0 t d : ℝ) (hs0 : 0 < s0) (hs0q : s0 ^ 2 ≤ q)
    (hU : log q ≤ U) (hL0 : L0 ≤ log q) (hL0p : 0 < L0)
    (ht : 3 / (((q - 1) / 2 : ℕ) : ℝ) ≤ t) (hd : d ≤ 1 / q)
    (hX : -U / 2 + (log 2 + 1 - 2 / L0) - 2 / 3 - t + d ≤ 0)
    (hfin : 1 ≤ s0 * (1 + (-U / 2 + (log 2 + 1 - 2 / L0) - 2 / 3 - t + d) / 3.1415)) :
    1 ≤ 1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
      sqrt q / π * (log (((q - 1) / 2 : ℕ) : ℝ) + eulerMascheroniConstant + log 2 +
        3 / (((q - 1) / 2 : ℕ) : ℝ)) := by
  set H := (q - 1) / 2 with hHdef
  have hH3 : 3 ≤ H := by omega
  have h2H : 2 * H + 1 ≤ q := by omega
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH3
  have h2Hr : 2 * (H : ℝ) + 1 ≤ q := by exact_mod_cast h2H
  have hqr : (7 : ℝ) ≤ q := by exact_mod_cast hq7
  have hqpos : (0 : ℝ) < q := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  set L := log (q : ℝ) with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le hL0p hL0
  -- log L ≥ log 2 + 1 - 2/L0
  have hlogL : log 2 + 1 - 2 / L0 ≤ log L := by
    have e : log L = log 2 + log (L / 2) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < L / 2 by positivity)
    have h2 : (L / 2)⁻¹ = 2 / L := by rw [inv_div]
    have h3 : 2 / L ≤ 2 / L0 := div_le_div_of_nonneg_left (by norm_num) hL0p hL0
    rw [e]; rw [h2] at h1; linarith
  -- D ≥ 1/q
  have hD : 1 / (q : ℝ) ≤ L - (log H + log 2) := by
    have e : log H + log 2 = log (2 * H) := by
      rw [Real.log_mul (by norm_num) hHpos.ne']; ring
    have e2 : L - log (2 * H) = log (q / (2 * H)) := by
      rw [Real.log_div hqpos.ne' (by positivity)]
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < (q : ℝ) / (2 * H) by positivity)
    have h2 : 1 / (q : ℝ) ≤ 1 - ((q : ℝ) / (2 * H))⁻¹ := by
      rw [inv_div, div_le_iff₀' hqpos] ; rw [mul_sub, mul_one, mul_div_assoc', mul_comm (q:ℝ) (2 * H),
        ← mul_div_assoc', div_self hqpos.ne', mul_one] ; linarith
    rw [e, e2]; linarith
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi := Real.pi_gt_d4
  set Y := L / 2 + log L - log H - eulerMascheroniConstant - log 2 - 3 / H with hY
  set X := -U / 2 + (log 2 + 1 - 2 / L0) - 2 / 3 - t + d with hXdef
  have hYX : X ≤ Y := by rw [hY, hXdef]; linarith
  have hE : 1 / (2 * π) * sqrt q * L + 1 / π * sqrt q * log L + sqrt q -
      sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H) = sqrt q * (1 + Y / π) := by
    rw [hY]; field_simp; ring
  rw [hE]
  have hdiv : X / 3.1415 ≤ Y / π := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have hs : s0 ≤ sqrt q := Real.le_sqrt_of_sq_le hs0q
  have hpos : 0 ≤ 1 + X / 3.1415 := by
    by_contra hc; have hc' := not_le.mp hc; nlinarith
  nlinarith


/-- The core estimate on a dyadic range 2^k < q ≤ 2^(k+1). PROVED. -/
theorem remainder_dyadic {q : ℕ} (hq7 : 7 ≤ q) (k : ℕ) (hk : 3 ≤ k) (hlo : 2 ^ k + 1 ≤ q) (hhi : q ≤ 2 ^ (k + 1))
    (s0 : ℝ) (hs0 : 0 < s0) (hs0q : s0 ^ 2 ≤ 2 ^ k + 1)
    (hX : -((k + 1) * 0.6932) / 2 + (log 2 + 1 - 2 / (k * 0.6931)) - 2 / 3 - 3 / 2 ^ (k - 1) +
      1 / 2 ^ (k + 1) ≤ 0)
    (hfin : 1 ≤ s0 * (1 + (-((k + 1) * 0.6932) / 2 + (log 2 + 1 - 2 / (k * 0.6931)) - 2 / 3 -
      3 / 2 ^ (k - 1) + 1 / 2 ^ (k + 1)) / 3.1415)) :
    1 ≤ 1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
      sqrt q / π * (log (((q - 1) / 2 : ℕ) : ℝ) + eulerMascheroniConstant + log 2 +
        3 / (((q - 1) / 2 : ℕ) : ℝ)) := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hlor : ((2 ^ k + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hlo
  have hhir : (q : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hhi
  push_cast at hlor hhir
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  refine remainder_core hq7 s0 ((k + 1) * 0.6932) (k * 0.6931) (3 / 2 ^ (k - 1)) (1 / 2 ^ (k + 1)) hs0
    (by linarith) ?_ ?_ (by positivity) ?_ ?_ hX hfin
  · calc log q ≤ log ((2 : ℝ) ^ (k + 1)) := Real.log_le_log (by linarith) hhir
      _ = (k + 1) * log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (k + 1) * 0.6932 := by gcongr; linarith
  · calc (k : ℝ) * 0.6931 ≤ k * log 2 := by gcongr; linarith
      _ = log ((2 : ℝ) ^ k) := by rw [Real.log_pow]
      _ ≤ log q := Real.log_le_log hp (by linarith)
  · have hH : 2 ^ (k - 1) ≤ (q - 1) / 2 := by
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have hHr : ((2 ^ (k - 1) : ℕ) : ℝ) ≤ (((q - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hH
    push_cast at hHr
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hHr
  · have : (q : ℝ) ≤ 2 ^ (k + 1) := hhir
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) this

/-- The core estimate for q = 7, 8, the tightest case. PROVED. -/
theorem remainder_small {q : ℕ} (hq7 : 7 ≤ q) (hq8 : q ≤ 8) :
    1 ≤ 1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
      sqrt q / π * (log (((q - 1) / 2 : ℕ) : ℝ) + eulerMascheroniConstant + log 2 +
        3 / (((q - 1) / 2 : ℕ) : ℝ)) := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hqr : (7 : ℝ) ≤ q := by exact_mod_cast hq7
  have hqr' : (q : ℝ) ≤ 8 := by exact_mod_cast hq8
  have hH : (q - 1) / 2 = 3 := by omega
  refine remainder_core hq7 2.64 (3 * 0.6932) 1.93 1 (1 / 8) (by norm_num) (by nlinarith) ?_ ?_
    (by norm_num) ?_ ?_ ?_ ?_
  · calc log q ≤ log ((2 : ℝ) ^ 3) := Real.log_le_log (by linarith) (by norm_num; linarith)
      _ = 3 * log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 3 * 0.6932 := by linarith
  · have e : log (8 : ℝ) = 3 * log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 7 / 8 by norm_num)
    have e2 : log ((7 : ℝ) / 8) = log 7 - log 8 := Real.log_div (by norm_num) (by norm_num)
    have h3 : log (7 : ℝ) ≤ log q := Real.log_le_log (by norm_num) hqr
    norm_num at h1
    linarith
  · rw [hH]; norm_num
  · exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hqr'
  · norm_num; linarith
  · norm_num; nlinarith

/-- The final arithmetic of the full length case, the remainder of `PVCases1122.odd_truncated`
at H = (q-1)/2 is at least 1, which absorbs the constant part -(χ(N+1) - χ(M))/2 of Frolenkov
display 12. Numerically the remainder is at least 1 for 7 ≤ q ≤ 14762, about 1.11 at q = 7, and
first below 1 at q = 14763. PROVED, by dyadic ranges up to 1024. -/
theorem remainder_ge_one {q : ℕ} (hq7 : 7 ≤ q) (hq : q ≤ 1000) :
    1 ≤ 1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
      sqrt q / π * (log (((q - 1) / 2 : ℕ) : ℝ) + eulerMascheroniConstant + log 2 +
        3 / (((q - 1) / 2 : ℕ) : ℝ)) := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  rcases Nat.lt_or_ge q 9 with h | h
  · exact remainder_small hq7 (by omega)
  rcases Nat.lt_or_ge q 17 with h1 | h1
  · exact remainder_dyadic hq7 3 le_rfl (by norm_num; omega) (by norm_num; omega) 3 (by norm_num)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases Nat.lt_or_ge q 33 with h2 | h2
  · exact remainder_dyadic hq7 4 (by norm_num) (by norm_num; omega) (by norm_num; omega) 4 (by norm_num)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases Nat.lt_or_ge q 65 with h3 | h3
  · exact remainder_dyadic hq7 5 (by norm_num) (by norm_num; omega) (by norm_num; omega) 5.7 (by norm_num)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases Nat.lt_or_ge q 129 with h4 | h4
  · exact remainder_dyadic hq7 6 (by norm_num) (by norm_num; omega) (by norm_num; omega) 8 (by norm_num)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases Nat.lt_or_ge q 257 with h5 | h5
  · exact remainder_dyadic hq7 7 (by norm_num) (by norm_num; omega) (by norm_num; omega) 11.3 (by norm_num)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases Nat.lt_or_ge q 513 with h6 | h6
  · exact remainder_dyadic hq7 8 (by norm_num) (by norm_num; omega) (by norm_num; omega) 16 (by norm_num)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  · exact remainder_dyadic hq7 9 (by norm_num) (by norm_num; omega) (by norm_num; omega) 22.6 (by norm_num)
      (by norm_num) (by norm_num; linarith) (by norm_num; linarith)

/-- LEAF: Pomerance 2011 proof of Theorem 1 for odd χ, large moduli q > 1000: the Polya Fourier
expansion of the interval indicator, Frolenkov display 12, truncated at Pomerance's parameter H
with his explicit truncation error, Frolenkov displays 15 and 21, reduced through display 10 and
|τ(χ)| = √q, Frolenkov displays 13, 14 and 22; here the full length bound `odd_full_bound` no
longer suffices, the remainder at H = (q-1)/2 being below 1 from q = 14763 on and of size
-√q log q/(2π) asymptotically, so cancellation in the h sum beyond H is needed. Class HARD. -/
theorem odd_truncated_large {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 1000 < q) (hodd : χ (-1) ≠ 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  sorry

/-- Assembly: exactly `PVCases1122.odd_truncated`. For q ≤ 1000, H = (q-1)/2 with
`odd_full_bound` and `remainder_ge_one`; for q > 1000, the LEAF `odd_truncated_large`. -/
theorem odd_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  by_cases hQ : q ≤ 1000
  · refine ⟨(q - 1) / 2, by omega, fun M N => ?_⟩
    have a := odd_full_bound χ hχ hq7 hodd M N
    have b := remainder_ge_one hq7 hQ
    linarith
  · exact odd_truncated_large χ hχ (by omega) hodd

example : type_of% @odd_truncated =
    type_of% @LeanLab.HelfgottMajor.PVCases1122.odd_truncated := rfl

end LeanLab.HelfgottMajor.PVOddTrunc1122

#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.cot_le
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.odd_cot_bound
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.odd_full_bound
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.remainder_core
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.remainder_dyadic
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.remainder_small
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.remainder_ge_one
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.odd_truncated_large
#print axioms LeanLab.HelfgottMajor.PVOddTrunc1122.odd_truncated
