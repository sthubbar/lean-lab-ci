import Mathlib
import LeanLab.HelfgottMajor.PVEvenTrunc1122
import LeanLab.HelfgottMajor.PVCotTail1122

/-!
Route burst S124, burst-20261122, step even-truncated-p2.
Split of the HARD LEAF `PVEvenTrunc1122.cot_tail` by the size of q.

For q at most 64 take H = (q - 1)/2, the largest H with 2H < q: then every h in the tail range
H < h < q - H has 2h = q, so sin(2π K h/q) = sin(π K) = 0 and the tail vanishes, and cot_tail
reduces to the budget being at least 1/2, an explicit real inequality, PROVED here for q up to 64;
q from 2 to 4 carries no even primitive character, PROVED. For q above 64 the tail is
the real content of Pomerance's truncation, Frolenkov displays 15 and 16, kept as the LEAF
`cot_tail_large`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail

open Real Finset

/-- With H = (q - 1)/2 the tail of the cotangent sum vanishes: every h with H < h < q - H has
2h = q, so sin(2π K h/q) = sin(π K) = 0. PROVED. -/
theorem tail_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K : ℕ) :
    ∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ (q - 1) / 2 ∨ q - (q - 1) / 2 ≤ h.val)),
      χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) = 0 := by
  refine sum_eq_zero fun h hh => ?_
  simp only [mem_filter, mem_univ, true_and] at hh
  have h2 : 2 * h.val = q := by omega
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h2r : (2 : ℝ) * h.val = q := by exact_mod_cast h2
  have e : 2 * π * K * (h.val : ℝ) / q = (K : ℕ) * π := by
    have hv : (h.val : ℝ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h2r; exact hq0 h2r.symm
    rw [← h2r]; field_simp
  rw [e, sin_nat_mul_pi, mul_zero, Complex.ofReal_zero, mul_zero]

/-- LEAF: Pomerance 2011 proof of Theorem 1, even case, the truncation error with Pomerance's
choice of H, Frolenkov displays 15 and 16, for q above 64, where the budget at the largest H
no longer suffices for every q and the tail must be bounded. Class HARD. -/
theorem cot_tail_large {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (hbig : 64 < q) :
    ∃ H : ℕ, 1 ≤ H ∧ 2 * H < q ∧ ∀ K : ℕ,
      ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
          ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
          (2 * sqrt q) + 1 / 2 ≤
        1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
  exact PVCotTail1122.cot_tail χ hχ hq heven

/-- Arithmetic helper for `budget_small`. PROVED. -/
theorem fin_mul {s X P a b : ℝ} (hs : a ≤ s) (hX : b ≤ X) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : P ≤ 2 * a * b) : 1 / 2 * P ≤ s * X := by
  nlinarith [mul_le_mul hs hX hb (ha.trans hs)]

/-- Arithmetic helper for `budget_small`: c ≤ √x from c² ≤ x. PROVED. -/
theorem sqrt_ge {x c : ℝ} (hc : 0 ≤ c) (h : c ^ 2 ≤ x) : c ≤ sqrt x := by
  rw [show c = sqrt (c ^ 2) by rw [sqrt_sq hc]]
  exact sqrt_le_sqrt h

/-- Arithmetic helper for `budget_small`: log x ≤ k log 2 for x ≤ 2^k. PROVED. -/
theorem log_le_pow_two {x : ℝ} (k : ℕ) (hx : 0 < x) (h : x ≤ 2 ^ k) : log x ≤ k * log 2 := by
  rw [← Real.log_pow]; exact log_le_log hx h

/-- The explicit inequality for small q in Pomerance's even case: for 5 ≤ q ≤ 64 the budget
at H = (q - 1)/2 is at least the endpoint term 1/2. Was a leaf of class EASY in the first S124 commit; PROVED. -/
theorem budget_small {q : ℕ} (h5 : 5 ≤ q) (h64 : q ≤ 64) :
    1 / 2 ≤ 1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
      2 / π ^ 2 * sqrt q * (log (((q - 1) / 2 : ℕ) : ℝ) + eulerMascheroniConstant + log 2 +
        3 / (((q - 1) / 2 : ℕ) : ℝ)) := by
  have hH2 : 2 ≤ (q - 1) / 2 := by omega
  have h2H : 2 * ((q - 1) / 2) ≤ q := by omega
  generalize hHd : (q - 1) / 2 = H at hH2 h2H
  have hqr : (5 : ℝ) ≤ q := by exact_mod_cast h5
  have hq0 : (0 : ℝ) < q := by linarith
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH2
  have hH0 : (0 : ℝ) < H := by linarith
  have h2Hr : 2 * (H : ℝ) ≤ q := by exact_mod_cast h2H
  have hP1 := pi_gt_d2
  have hP2 := pi_lt_d4
  have hPa : 9.8596 ≤ π ^ 2 := by nlinarith
  have hPb : π ^ 2 ≤ 9.8697 := by nlinarith
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := log_two_gt_d9
  have hl2' := log_two_lt_d9
  have hL4 : 2 * log 2 ≤ log (q : ℝ) := by
    have e4 : (2 : ℝ) * log 2 = log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [e4]; exact log_le_log (by norm_num) (by linarith)
  set L := log (q : ℝ) with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hLL0 : 0 ≤ log L := log_nonneg hL1
  have hLL := one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < L)
  have hlogH : log (H : ℝ) ≤ L - log 2 := by
    rw [hLdef, ← Real.log_div (by linarith) (by norm_num)]
    exact log_le_log hH0 (by linarith)
  set s := sqrt (q : ℝ) with hsdef
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hpi0 : 0 < π ^ 2 := by positivity
  have hrw : 1 / π ^ 2 * s * L + 2 / π ^ 2 * s * log L + 3 / 4 * s -
      2 / π ^ 2 * s * (log (H : ℝ) + eulerMascheroniConstant + log 2 + 3 / (H : ℝ)) =
      s * (L + 2 * log L + 3 / 4 * π ^ 2 -
        2 * (log (H : ℝ) + eulerMascheroniConstant + log 2 + 3 / (H : ℝ))) / π ^ 2 := by
    field_simp
  rw [hrw, le_div_iff₀ hpi0]
  rcases (by omega : q ≤ 6 ∨ (7 ≤ q ∧ q ≤ 8) ∨ (9 ≤ q ∧ q ≤ 16) ∨ (17 ≤ q ∧ q ≤ 32) ∨ 33 ≤ q)
    with hc | hc | hc | hc | hc
  · have hH : H = 2 := by omega
    subst hH
    have hinv : L⁻¹ ≤ 1 / 1.3862 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hs : (2.236 : ℝ) ≤ s := sqrt_ge (by norm_num) (by linarith)
    refine fin_mul hs (b := 2.21) ?_ (by norm_num) (by norm_num) (by linarith)
    push_cast
    have : (3 : ℝ) / 2 = 1.5 := by norm_num
    rw [this]
    nlinarith
  · have hH3 : (3 : ℝ) ≤ H := by exact_mod_cast (by omega : 3 ≤ H)
    have hd : 3 / (H : ℝ) ≤ 3 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH3
    have hLu := log_le_pow_two 3 hq0 (by norm_num; exact_mod_cast (by omega : q ≤ 8))
    have hs : (2.645 : ℝ) ≤ s := sqrt_ge (by norm_num) (by
      have : (7 : ℝ) ≤ q := by exact_mod_cast hc.1
      linarith)
    refine fin_mul hs (b := 1.9) ?_ (by norm_num) (by norm_num) (by linarith)
    push_cast at hLu
    nlinarith
  · have hH3 : (4 : ℝ) ≤ H := by exact_mod_cast (by omega : 4 ≤ H)
    have hd : 3 / (H : ℝ) ≤ 3 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH3
    have hLu := log_le_pow_two 4 hq0 (by norm_num; exact_mod_cast (by omega : q ≤ 16))
    have hs : (3 : ℝ) ≤ s := sqrt_ge (by norm_num) (by
      have : (9 : ℝ) ≤ q := by exact_mod_cast hc.1
      linarith)
    refine fin_mul hs (b := 1.7) ?_ (by norm_num) (by norm_num) (by linarith)
    push_cast at hLu
    nlinarith
  · have hH3 : (8 : ℝ) ≤ H := by exact_mod_cast (by omega : 8 ≤ H)
    have hd : 3 / (H : ℝ) ≤ 3 / 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH3
    have hLu := log_le_pow_two 5 hq0 (by norm_num; exact_mod_cast (by omega : q ≤ 32))
    have hs : (4.123 : ℝ) ≤ s := sqrt_ge (by norm_num) (by
      have : (17 : ℝ) ≤ q := by exact_mod_cast hc.1
      linarith)
    refine fin_mul hs (b := 1.8) ?_ (by norm_num) (by norm_num) (by linarith)
    push_cast at hLu
    nlinarith
  · have hH3 : (16 : ℝ) ≤ H := by exact_mod_cast (by omega : 16 ≤ H)
    have hd : 3 / (H : ℝ) ≤ 3 / 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH3
    have hLu := log_le_pow_two 6 hq0 (by norm_num; exact_mod_cast (by omega : q ≤ 64))
    have hs : (5.744 : ℝ) ≤ s := sqrt_ge (by norm_num) (by
      have : (33 : ℝ) ≤ q := by exact_mod_cast hc
      linarith)
    refine fin_mul hs (b := 1.5) ?_ (by norm_num) (by norm_num) (by linarith)
    push_cast at hLu
    nlinarith


/-- There is no even primitive Dirichlet character modulo q for 2 ≤ q ≤ 4, the units mod 3
and mod 4 being ±1 and the only character mod 2 being trivial. PROVED. -/
theorem no_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (h4 : q ≤ 4) : False := by
  have hc : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).mp hχ
  have h2 : 2 ≤ q := by have := NeZero.ne q; omega
  have h1 : χ = 1 := by
    ext a
    rw [MulChar.one_apply_coe]
    interval_cases q
    · have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
      rw [key _ _ a.val_inv, map_one]
    · have key : ∀ x y : ZMod 3, x * y = 1 → x = 1 ∨ x = -1 := by decide
      rcases key _ _ a.val_inv with h | h
      · rw [h, map_one]
      · rw [h, heven]
    · have key : ∀ x y : ZMod 4, x * y = 1 → x = 1 ∨ x = -1 := by decide
      rcases key _ _ a.val_inv with h | h
      · rw [h, map_one]
      · rw [h, heven]
  rw [h1, DirichletCharacter.conductor_one] at hc
  exact hq hc.symm

/-- Assembly: exactly `PVEvenTrunc1122.cot_tail`, from `tail_zero`, `budget_small`, `no_small`
and the LEAF `cot_tail_large`. -/
theorem cot_tail_of_leaves {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ 2 * H < q ∧ ∀ K : ℕ,
      ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
          ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
          (2 * sqrt q) + 1 / 2 ≤
        1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
  by_cases hbig : 64 < q
  · exact cot_tail_large χ hχ hq heven hbig
  by_cases h4 : q ≤ 4
  · exact (no_small χ hχ hq heven h4).elim
  refine ⟨(q - 1) / 2, by omega, by omega, fun K => ?_⟩
  rw [tail_zero χ K, norm_zero, zero_div, zero_add]
  exact budget_small (by omega) (by omega)

example : type_of% @cot_tail_of_leaves =
    type_of% @LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_tail := rfl

end LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail

#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.tail_zero
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.cot_tail_large
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.fin_mul
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.sqrt_ge
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.log_le_pow_two
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.budget_small
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.no_small
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.cot_tail_of_leaves
