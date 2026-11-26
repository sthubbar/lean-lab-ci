import Mathlib
import LeanLab.HelfgottMajor.PVCases1122
import LeanLab.HelfgottMajor.PVEvenPolya1122

/-!
Route burst S68, burst-20261122, tag even-truncated.
Split of the HARD LEAF `PVCases1122.even_truncated`, Pomerance 2011 Theorem 1, even case, in
the form of Frolenkov arXiv 1107.0381 displays 12 to 17, into three strictly smaller pieces:

1. `cot_identity`, the exact finite Polya expansion for even primitive χ, obtained from
   `PVEvenPolya1122.polya_initial_segment` by summing the geometric inner sum in closed form and
   pairing h with -h: `τ(χ⁻¹) (2 S(K) + χ(K)) = ∑_h χ⁻¹(h) cot(π h/q) sin(2π K h/q)`.
   This is Frolenkov display 12 with M = 0 and display 17 before truncation, and Pomerance's
   display 10 route. Numerically checked to 1e-13 for every even primitive χ, q below 60.
2. `cot_head`, the head h ≤ H and h ≥ q - H, bounded through cot y ≤ 1/y on (0, π/2):
   the step from the cotangent weights to √q/π ∑_{j ≤ H} |sin(j x)|/j, Frolenkov display 17.
3. `cot_tail`, the truncation error, the range H < h < q - H, together with Pomerance's choice of
   H and the endpoint term 1/2: it must fit in the budget left after Lemma 3.
The norm `|τ(χ⁻¹)| = √q`, Frolenkov display 13, is PROVED from `PV420Split1122.norm_gauss`,
and the assembly `even_truncated` has exactly the statement of the LEAF in `PVCases1122`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVEvenTrunc1122

open Real Finset

/-- Frolenkov display 13 for χ⁻¹: `|τ(χ⁻¹)| = √q` for χ primitive. PROVED. -/
theorem norm_gauss_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ = sqrt q :=
  LeanLab.HelfgottMajor.PV420Split1122.norm_gauss
    (LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ)

/-- The elementary bound used in the head step, Frolenkov display 17: for 0 < y < π/2,
`0 < cot y ≤ 1/y`, from y < tan y. PROVED. -/
theorem cot_pos_le_inv {y : ℝ} (h0 : 0 < y) (h1 : y < π / 2) : 0 < cot y ∧ cot y ≤ 1 / y := by
  have ht := tan_pos_of_pos_of_lt_pi_div_two h0 h1
  have hl := lt_tan h0 h1
  have hc : cot y = 1 / tan y := by
    rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, one_div_div]
  rw [hc]
  exact ⟨one_div_pos.mpr ht, one_div_le_one_div_of_le h0 hl.le⟩

/-- The closed form of the paired geometric inner sum inside `cot_identity`, Frolenkov display 17
before truncation: for sin φ ≠ 0, `2 ∑_{m<K} cos(2mφ) = 1 - cos(2Kφ) + sin(2Kφ) cot φ`; with
φ = πh/q, the left side is the sum of e(mh/q) + e(-mh/q) over m < K. PROVED. -/
theorem cos_sum_cot (φ : ℝ) (hφ : sin φ ≠ 0) (K : ℕ) :
    2 * ∑ m ∈ range K, cos (m * (2 * φ)) =
      1 - cos (K * (2 * φ)) + sin (K * (2 * φ)) * cot φ := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    have e1 : ((K : ℝ) + 1) * (2 * φ) = K * (2 * φ) + 2 * φ := by ring
    rw [e1, cos_add, sin_add, cos_two_mul, sin_two_mul, cot_eq_cos_div_sin]
    field_simp
    linear_combination (-2 * sin (K * 2 * φ) * cos φ) * sin_sq_add_cos_sq φ

/-- The cosine as an average of `stdAddChar` values. PROVED. -/
private theorem cos_eq_stdAddChar {q : ℕ} [NeZero q] (n : ℕ) (h : ZMod q) :
    ((cos (2 * π * n * (h.val : ℝ) / q) : ℝ) : ℂ) =
      (ZMod.stdAddChar ((n : ZMod q) * h) + ZMod.stdAddChar (-((n : ZMod q) * h))) / 2 := by
  have e1 : (n : ZMod q) * h = (((n * h.val : ℕ) : ℤ) : ZMod q) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have e2 : -((n : ZMod q) * h) = ((-((n * h.val : ℕ) : ℤ) : ℤ) : ZMod q) := by
    rw [e1]; push_cast; ring
  rw [e2, e1, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, Complex.ofReal_cos, Complex.cos]
  push_cast
  congr 3 <;> ring_nf

/-- The cosine twisted Gauss sum: `∑_h χ⁻¹(h) cos(2π n h/q) = χ(n) τ(χ⁻¹)`. PROVED. -/
private theorem cos_twist {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (heven : χ (-1) = 1) (n : ℕ) :
    ∑ h : ZMod q, χ⁻¹ h * ((cos (2 * π * n * (h.val : ℝ) / q) : ℝ) : ℂ) =
      χ (n : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχ' := LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ
  have heven' : χ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', heven, inv_one]
  have := LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_even hχ' heven' (n : ZMod q)
  rw [inv_inv] at this
  rw [this]
  exact sum_congr rfl fun h _ => by rw [cos_eq_stdAddChar]

/-- The sum of `χ⁻¹` vanishes for `χ` primitive and `q ≠ 1`. PROVED. -/
private theorem sum_inv_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) : ∑ h : ZMod q, χ⁻¹ h = 0 := by
  have hχ' := LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ
  refine MulChar.sum_eq_zero_of_ne_one fun h1 => hq ?_
  rw [DirichletCharacter.IsPrimitive, h1, DirichletCharacter.conductor_one] at hχ'
  exact hχ'.symm

/-- The termwise expansion: for every `h`, `χ⁻¹(h) cot(πh/q) sin(2πKh/q)` equals
`χ⁻¹(h) (2 ∑_{m<K} cos(2πmh/q) - 1 + cos(2πKh/q))`. PROVED. -/
private theorem term_expand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1) (K : ℕ)
    (h : ZMod q) :
    χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) =
      χ⁻¹ h * (2 * ∑ m ∈ range K, ((cos (2 * π * m * (h.val : ℝ) / q) : ℝ) : ℂ) - 1 +
        ((cos (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)) := by
  by_cases h0 : h = 0
  · subst h0
    have : χ⁻¹ (0 : ZMod q) = 0 := by
      have : Nontrivial (ZMod q) := by
        rw [ZMod.nontrivial_iff]; exact hq
      exact MulChar.map_zero _
    rw [this, zero_mul, zero_mul]
  · congr 1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hv0 : 0 < h.val := by
      rcases Nat.eq_zero_or_pos h.val with hv | hv
      · exact absurd ((ZMod.val_eq_zero h).1 hv) h0
      · exact hv
    have hvq : h.val < q := ZMod.val_lt h
    have hsin : sin (π * (h.val : ℝ) / q) ≠ 0 := by
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      · have : (0 : ℝ) < h.val := by exact_mod_cast hv0
        positivity
      · rw [div_lt_iff₀ hq0]
        have : (h.val : ℝ) < q := by exact_mod_cast hvq
        nlinarith [pi_pos]
    have key := cos_sum_cot _ hsin K
    have e : ∀ n : ℕ, (n : ℝ) * (2 * (π * (h.val : ℝ) / q)) = 2 * π * n * (h.val : ℝ) / q := by
      intro n; ring
    simp only [e] at key
    have key' : cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) =
        2 * ∑ m ∈ range K, cos (2 * π * m * (h.val : ℝ) / q) - 1 +
          cos (2 * π * K * (h.val : ℝ) / q) := by linarith
    rw [key']
    push_cast
    ring

/-- LEAF: Pomerance 2011 proof of Theorem 1, even case, the exact finite Fourier expansion,
Frolenkov display 12 with M = 0 and display 17 before truncation: from
`PVEvenPolya1122.polya_initial_segment`, the geometric inner sum is
`(e(Kh/q) - 1)/(e(h/q) - 1)`, whose real part is `1/2 + sin(2πKh/q) cot(πh/q)/2 - cos(2πKh/q)/2`;
pairing h with -h for even χ keeps the real part, the constant sums to 0 over h, and the cosine
part gives `χ(K) τ(χ⁻¹)` by `PV420Split1122.gauss_twist`. Class MEDIUM. -/
theorem cot_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (K : ℕ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * (2 * ∑ m ∈ range K, χ (m : ZMod q) + χ (K : ZMod q)) =
      ∑ h : ZMod q, χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) := by

  simp_rw [term_expand χ hq K]
  simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, mul_sum]
  rw [sum_inv_eq_zero hχ hq, cos_twist hχ heven K, sum_comm]
  have : ∀ m ∈ range K, ∑ h : ZMod q, χ⁻¹ h * (2 * ((cos (2 * π * m * (h.val : ℝ) / q) : ℝ) : ℂ))
      = 2 * (χ (m : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) := by
    intro m _
    rw [← cos_twist hχ heven m, mul_sum]
    exact sum_congr rfl fun h _ => by ring
  rw [sum_congr rfl this, sub_zero]
  congr 1
  · exact sum_congr rfl fun i _ => by ring
  · ring

/-- Reflection used in the head step, Frolenkov display 17: the weight |cot(π v/q)| |sin(2π K v/q)|
is unchanged under v ↦ q - v. PROVED. -/
theorem F_reflect {q : ℕ} (hq0 : (0:ℝ) < q) (K j : ℕ) (hj : j ≤ q) :
    |cot (π * ((q - j : ℕ) : ℝ) / q)| * |sin (2 * π * K * ((q - j : ℕ) : ℝ) / q)| =
      |cot (π * (j : ℝ) / q)| * |sin (2 * π * K * (j : ℝ) / q)| := by
  have hc : ((q - j : ℕ) : ℝ) = q - j := by push_cast [Nat.cast_sub hj]; ring
  rw [hc]
  have e1 : π * ((q:ℝ) - j) / q = π - π * j / q := by field_simp
  have e2 : 2 * π * K * ((q:ℝ) - j) / q = (2 * K : ℕ) * π - 2 * π * K * j / q := by
    push_cast; field_simp
  rw [e1, e2, cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_pi_sub, sin_pi_sub, sin_sub,
    sin_nat_mul_pi, cos_nat_mul_pi]
  have : ((-1:ℝ) ^ (2 * K)) = 1 := by rw [pow_mul]; simp
  rw [this]
  simp [abs_div, abs_neg]

/-- The head step termwise, Frolenkov display 17: for 1 ≤ j ≤ H with 2H < q,
|cot(π j/q)| |sin(2π K j/q)| ≤ q/π · |sin(j x)|/j, from `cot_pos_le_inv`. PROVED. -/
theorem F_le {q : ℕ} (hq0 : (0:ℝ) < q) (K j H : ℕ) (hj1 : 1 ≤ j) (hjH : j ≤ H) (hHq : 2 * H < q) :
    |cot (π * (j : ℝ) / q)| * |sin (2 * π * K * (j : ℝ) / q)| ≤
      q / π * (|sin (j * (2 * π * K / q))| / j) := by
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj1
  have hy0 : 0 < π * (j:ℝ) / q := by positivity
  have h2 : (2 * j : ℝ) < q := by
    have : 2 * j < q := by omega
    exact_mod_cast this
  have hy1 : π * (j:ℝ) / q < π / 2 := by
    rw [div_lt_div_iff₀ hq0 two_pos]; nlinarith [pi_pos]
  obtain ⟨hp, hl⟩ := LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_pos_le_inv hy0 hy1
  rw [abs_of_pos hp]
  have e : 2 * π * K * (j:ℝ) / q = j * (2 * π * K / q) := by ring
  rw [e]
  have hs := abs_nonneg (sin (j * (2 * π * K / q)))
  have : 1 / (π * j / q) = q / π * (1 / j) := by field_simp
  calc cot (π * j / q) * |sin (j * (2 * π * K / q))| ≤ 1 / (π * j / q) * |sin (j * (2 * π * K / q))| :=
        mul_le_mul_of_nonneg_right hl hs
    _ = q / π * (|sin (j * (2 * π * K / q))| / j) := by rw [this]; ring

/-- Pomerance 2011 proof of Theorem 1, even case, the head of the cotangent sum,
Frolenkov display 17: for 1 ≤ H and 2H < q, the terms with h ≤ H or h ≥ q - H pair up by
h ↦ q - h, and 0 < cot y ≤ 1/y on (0, π/2] gives the bound √q/π ∑_{j ≤ H} |sin(j x)|/j with
x = 2πK/q, after division by 2√q. Was LEAF MEDIUM in the first S68 commit; now PROVED. -/
theorem cot_head {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (H : ℕ) (hH : 1 ≤ H)
    (hHq : 2 * H < q) (K : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
        (2 * sqrt q) ≤
      sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set F : ℕ → ℝ := fun v => |cot (π * (v : ℝ) / q)| * |sin (2 * π * K * (v : ℝ) / q)| with hF
  have step1 : ‖∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ ≤
      ∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), F h.val := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun h _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have := DirichletCharacter.norm_le_one χ⁻¹ h
    have hn : 0 ≤ |cot (π * (h.val : ℝ) / q)| * |sin (2 * π * K * (h.val : ℝ) / q)| := by
      positivity
    calc ‖χ⁻¹ h‖ * (|cot (π * (h.val : ℝ) / q)| * |sin (2 * π * K * (h.val : ℝ) / q)|)
        ≤ 1 * (|cot (π * (h.val : ℝ) / q)| * |sin (2 * π * K * (h.val : ℝ) / q)|) :=
          mul_le_mul_of_nonneg_right this hn
      _ = F h.val := by rw [one_mul]
  have step2 : ∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), F h.val =
      ∑ v ∈ (range q).filter (fun v => v ≤ H ∨ q - H ≤ v), F v := by
    refine sum_nbij (fun h : ZMod q => h.val) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      simp only [mem_filter, mem_range]
      exact ⟨ZMod.val_lt a, ha⟩
    · intro a _ b _ hab
      exact ZMod.val_injective q hab
    · intro v hv
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hv
      refine ⟨(v : ZMod q), ?_, ?_⟩
      · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
        rw [ZMod.val_cast_of_lt hv.1]; exact hv.2
      · simp only; rw [ZMod.val_cast_of_lt hv.1]
    · intro a _; rfl
  have hsplit : (range q).filter (fun v => v ≤ H ∨ q - H ≤ v) = range (H + 1) ∪ Ico (q - H) q := by
    ext v; simp only [mem_filter, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range (H + 1)) (Ico (q - H) q) := by
    rw [disjoint_left]; intro v h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
  have hF0 : F 0 = 0 := by simp [hF]
  have hA : ∑ v ∈ range (H + 1), F v = ∑ k ∈ range H, F (k + 1) := by
    rw [sum_range_succ', hF0, add_zero]
  have hB : ∑ v ∈ Ico (q - H) q, F v = ∑ k ∈ range H, F (k + 1) := by
    rw [sum_Ico_eq_sum_range, show q - (q - H) = H by omega, ← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [show q - H + (H - 1 - k) = q - (k + 1) by omega]
    exact F_reflect hq0 K (k + 1) (by omega)
  have hC : ∑ k ∈ range H, F (k + 1) ≤
      ∑ k ∈ range H, q / π * (|sin (((k + 1 : ℕ) : ℝ) * (2 * π * K / q))| / ((k + 1 : ℕ) : ℝ)) :=
    sum_le_sum fun k hk => F_le hq0 K (k + 1) H (by omega) (by rw [mem_range] at hk; omega) hHq
  have hD : ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j =
      ∑ k ∈ range H, |sin (((k + 1 : ℕ) : ℝ) * (2 * π * K / q))| / ((k + 1 : ℕ) : ℝ) := by
    rw [show Icc 1 H = Ico 1 (H + 1) by ext v; simp only [mem_Icc, mem_Ico]; omega, sum_Ico_eq_sum_range,
      show H + 1 - 1 = H by omega]
    refine sum_congr rfl fun k _ => ?_
    rw [add_comm 1 k]
  rw [← mul_sum] at hC
  rw [hD]
  set S := ∑ k ∈ range H, |sin (((k + 1 : ℕ) : ℝ) * (2 * π * K / q))| / ((k + 1 : ℕ) : ℝ)
  have hall : ‖∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ ≤
      2 * (q / π * S) := by
    rw [step2, hsplit, sum_union hdisj, hA, hB] at step1
    linarith
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  rw [div_le_iff₀ (by positivity)]
  have hqs : (q : ℝ) = sqrt q * sqrt q := (mul_self_sqrt hq0.le).symm
  calc _ ≤ 2 * (q / π * S) := hall
    _ = sqrt q / π * S * (2 * sqrt q) := by linear_combination (2 * S / π) * hqs

/-- LEAF: Pomerance 2011 proof of Theorem 1, even case, the truncation error with Pomerance's
choice of H, Frolenkov displays 15 and 16: there is H with 1 ≤ H and 2H < q so that the tail
H < h < q - H of the cotangent sum, divided by 2√q, plus the endpoint term 1/2, fits in the part
of the halved Pomerance even bound left after Lemma 3 at H. Class HARD.
Screened numerically for every even primitive χ, q from 5 to 200, see the notes. -/
theorem cot_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ 2 * H < q ∧ ∀ K : ℕ,
      ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
          ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
          (2 * sqrt q) + 1 / 2 ≤
        1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
  sorry

/-- From the exact identity and `|τ(χ⁻¹)| = √q`: `|S(K)| ≤ |∑_h …|/(2√q) + 1/2`. PROVED from the
LEAF `cot_identity`. -/
theorem initial_le_cot_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (K : ℕ) :
    ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
      ‖∑ h : ZMod q, χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
        (2 * sqrt q) + 1 / 2 := by
  have hid := cot_identity χ hχ hq heven K
  have hn := congrArg norm hid
  rw [norm_mul, norm_gauss_inv hχ] at hn
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  have hc : ‖χ (K : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  set S := ∑ m ∈ range K, χ (m : ZMod q)
  set T := ∑ h : ZMod q, χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)
  have h2 : ‖(2 : ℂ) * S‖ ≤ ‖2 * S + χ (K : ZMod q)‖ + ‖χ (K : ZMod q)‖ := by
    have := norm_sub_le (2 * S + χ (K : ZMod q)) (χ (K : ZMod q))
    simpa using this
  rw [norm_mul] at h2
  have h22 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h22] at h2
  have key : ‖2 * S + χ (K : ZMod q)‖ = ‖T‖ / sqrt q := by
    rw [eq_div_iff hs.ne', mul_comm]; exact hn
  rw [key] at h2
  have : ‖T‖ / (2 * sqrt q) = (‖T‖ / sqrt q) / 2 := by field_simp
  rw [this]
  linarith

/-- Assembly: exactly `PVCases1122.even_truncated`, from the LEAFs `cot_identity`, `cot_head`
and `cot_tail`. PROVED from them. -/
theorem even_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ K : ℕ,
      ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j +
        (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  obtain ⟨H, hH, hHq, htail⟩ := cot_tail χ hχ hq heven
  refine ⟨H, hH, fun K => ?_⟩
  have h1 := initial_le_cot_sum χ hχ hq heven K
  have h2 := cot_head χ hχ hq heven H hH hHq K
  have h3 := htail K
  have hsplit := (sum_filter_add_sum_filter_not univ
    (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val)
    (fun h : ZMod q => χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)))
  have htri := norm_add_le
    (∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ))
    (∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ))
  rw [hsplit] at htri
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hd : 0 < 2 * sqrt (q : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right htri hd.le
  rw [add_div] at hdiv
  linarith

example : type_of% @even_truncated =
    type_of% @LeanLab.HelfgottMajor.PVCases1122.even_truncated := rfl

end LeanLab.HelfgottMajor.PVEvenTrunc1122

#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.norm_gauss_inv
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_pos_le_inv
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.cos_sum_cot
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_identity
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.F_reflect
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.F_le
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_head
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_tail
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.initial_le_cot_sum
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122.even_truncated
