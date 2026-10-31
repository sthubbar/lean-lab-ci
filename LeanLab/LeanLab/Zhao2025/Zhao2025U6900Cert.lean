import Mathlib
import LeanLab.Zhao2025.Zhao2025U6841N0
import LeanLab.Zhao2025.Zhao2025U6841T5

/-!
# Zhao 2025, the 201 Theorem I counts of the `t₅` grid, interval certified from (3.26)

G. Zhao, "The exceptional set of Goldbach problem and Linnik's constant", arXiv 2511.05631v2,
a preprint.  Unit U-6900, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.  Binary Goldbach is open.

U-6841 proved `t5_sum_le`, the (3.27) sum at `Λ₀ = 1.363`, `λ₀ = 0.857` with the lab's integer
counts is at most `0.09063`, but only the first count `n₀ = 6` was certified from `G`; the other
200 were floats.  Here every count `nₖ = 6 + Σ_{i<k} jumpsᵢ`, `k = 0, …, 200`, is certified:
for each `k` a rational `xₖ ≥ 4λ₀/5` from gen/u6900_grid.py is checked by a kernel computation
over `ℚ` with the closed form `G_closed` and the Taylor enclosures of `e^{-a}` of
Pintz2018.Section9, so `(nₖ + 1)(Δ(xₖ, Λₖ, λ₀)² - ε) > 1` for every `ε ≤ 10⁻⁸`.

* `chk_sound`, PROVED: a passing rational check gives `0 < Δ` and `1/(Δ² - ε) < n + 1`.
* `gridOK_true`, PROVED by `decide +kernel`: all 201 checks pass.
* `count_le_of_326`, CONDITIONAL ON Zhao (3.26), Theorem I of Pintz, as the hypothesis `h326`:
  `N(Λₖ) ≤ nₖ` for every `k ≤ 200`.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6825 LeanLab.Zhao2025.U6841

/-! ### The rational checker -/

/-- `T15` over `ℚ`. -/
def T15q (y : ℚ) : ℚ := ∑ i ∈ Finset.range 15, y ^ i / (i.factorial : ℚ)

/-- The lower Taylor enclosure of `e^{-a}` over `ℚ`, valid for `0 ≤ a ≤ 8`. -/
def eloq (a : ℚ) : ℚ :=
  ((T15q (a / 8) + (a / 8) ^ 15 * (16 / ((Nat.factorial 15 : ℚ) * 15))) ^ 8)⁻¹

/-- The rational part of `G_closed`. -/
def Rq (z : ℚ) : ℚ := 16 / (15 * z) - 8 / (3 * z ^ 3) + 4 / z ^ 4 - 4 / z ^ 6

/-- Lower bound for `G(z)`, `0 < z`. -/
def G2lo (z : ℚ) : ℚ := 4 * (z + 1) ^ 2 * eloq (2 * z) / z ^ 6 + Rq z

/-- Upper bound for `G(z)`, `z < 0`. -/
def G1hi (z : ℚ) : ℚ := 4 * (z + 1) ^ 2 / (eloq (-2 * z) * z ^ 6) + Rq z

/-- Lower bound for `G(z)`, `z < 0`, from `e^{-2z} ≥ T15(-2z/8)⁸`. -/
def G1lo (z : ℚ) : ℚ := 4 * (z + 1) ^ 2 * T15q (-2 * z / 8) ^ 8 / z ^ 6 + Rq z

/-- The check at `(λ₀, Λ, x)` for the integer count `n`, with `ε = 10⁻⁸`. -/
def chk (l0 L x : ℚ) (n : ℕ) : Bool :=
  decide (4 * l0 / 5 ≤ x) && decide (0 < l0) && decide (l0 < L) &&
  decide (2 * ((L - l0) / x) ≤ 8) && decide (-2 * (-l0 / x) ≤ 8) &&
  decide (0 < eloq (2 * ((L - l0) / x))) && decide (0 < eloq (-2 * (-l0 / x))) &&
  decide (0 < G1lo (-l0 / x)) && decide (0 < G2lo ((L - l0) / x) - 8 / 45 * x) &&
  decide (1 < ((n : ℚ) + 1) *
    ((G2lo ((L - l0) / x) - 8 / 45 * x) ^ 2 / G1hi (-l0 / x) ^ 2 - 1 / 10 ^ 8))

/-! ### Soundness -/

theorem T15q_cast (y : ℚ) : ((T15q y : ℚ) : ℝ) = T15 (y : ℝ) := by
  unfold T15q T15; push_cast; rfl

theorem eloq_cast (a : ℚ) : ((eloq a : ℚ) : ℝ) =
    ((T15 ((a : ℝ) / 8) + ((a : ℝ) / 8) ^ 15 * (16 / ((Nat.factorial 15 : ℝ) * 15))) ^ 8)⁻¹ := by
  unfold eloq; push_cast; rw [T15q_cast]; push_cast; rfl

theorem eloq_le (a : ℚ) (h0 : 0 ≤ a) (h8 : a ≤ 8) : ((eloq a : ℚ) : ℝ) ≤ Real.exp (-(a : ℝ)) := by
  rw [eloq_cast]
  exact expneg_lower (a : ℝ) (by exact_mod_cast h0) (by exact_mod_cast h8)

theorem Gz_eq (z : ℝ) (hz : z ≠ 0) :
    Gz z = 4 * (z + 1) ^ 2 * Real.exp (-(2 * z)) / z ^ 6 +
      (16 / (15 * z) - 8 / (3 * z ^ 3) + 4 / z ^ 4 - 4 / z ^ 6) := G_closed z hz

theorem Rq_cast (z : ℚ) : ((Rq z : ℚ) : ℝ) =
    16 / (15 * (z : ℝ)) - 8 / (3 * (z : ℝ) ^ 3) + 4 / (z : ℝ) ^ 4 - 4 / (z : ℝ) ^ 6 := by
  unfold Rq; push_cast; rfl

theorem G2lo_le (z : ℚ) (hz : 0 < z) (h8 : 2 * z ≤ 8) : ((G2lo z : ℚ) : ℝ) ≤ Gz (z : ℝ) := by
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  rw [Gz_eq _ hz'.ne']
  unfold G2lo; push_cast; rw [Rq_cast]
  have he := eloq_le (2 * z) (by linarith) h8
  push_cast at he
  have hc : 0 ≤ 4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 := by positivity
  have := mul_le_mul_of_nonneg_left he hc
  have e1 : 4 * ((z : ℝ) + 1) ^ 2 * ((eloq (2 * z) : ℚ) : ℝ) / (z : ℝ) ^ 6 =
      4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * ((eloq (2 * z) : ℚ) : ℝ) := by ring
  have e2 : 4 * ((z : ℝ) + 1) ^ 2 * Real.exp (-(2 * (z : ℝ))) / (z : ℝ) ^ 6 =
      4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * Real.exp (-(2 * (z : ℝ))) := by ring
  rw [e1, e2]; linarith

theorem G1_bounds (z : ℚ) (hz : z < 0) (h8 : -2 * z ≤ 8) (hp : 0 < eloq (-2 * z)) :
    ((G1lo z : ℚ) : ℝ) ≤ Gz (z : ℝ) ∧ Gz (z : ℝ) ≤ ((G1hi z : ℚ) : ℝ) := by
  have hz' : (z : ℝ) < 0 := by exact_mod_cast hz
  rw [Gz_eq _ hz'.ne]
  unfold G1lo G1hi; push_cast; rw [Rq_cast]
  have he := eloq_le (-2 * z) (by linarith) h8
  push_cast at he
  have hp' : (0 : ℝ) < ((eloq (-2 * z) : ℚ) : ℝ) := by exact_mod_cast hp
  have hz6 : (0 : ℝ) < (z : ℝ) ^ 6 := Even.pow_pos (by decide) hz'.ne
  have hc : 0 ≤ 4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 := by positivity
  have hE1 : ((T15q (-2 * z / 8) : ℚ) : ℝ) ^ 8 ≤ Real.exp (-(2 * (z : ℝ))) := by
    rw [T15q_cast]
    have := exp_ge_T (-(2 * (z : ℝ))) (by linarith)
    convert this using 3; push_cast; ring
  have hE2 : Real.exp (-(2 * (z : ℝ))) * ((eloq (-2 * z) : ℚ) : ℝ) ≤ 1 := by
    calc _ ≤ Real.exp (-(2 * (z : ℝ))) * Real.exp (-(-2 * (z : ℝ))) :=
          mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hE3 : Real.exp (-(2 * (z : ℝ))) ≤ 1 / ((eloq (-2 * z) : ℚ) : ℝ) := by
    rw [le_div_iff₀ hp']; exact hE2
  constructor
  · have := mul_le_mul_of_nonneg_left hE1 hc
    have e1 : 4 * ((z : ℝ) + 1) ^ 2 * ((T15q (-2 * z / 8) : ℚ) : ℝ) ^ 8 / (z : ℝ) ^ 6 =
        4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * ((T15q (-2 * z / 8) : ℚ) : ℝ) ^ 8 := by ring
    have e2 : 4 * ((z : ℝ) + 1) ^ 2 * Real.exp (-(2 * (z : ℝ))) / (z : ℝ) ^ 6 =
        4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * Real.exp (-(2 * (z : ℝ))) := by ring
    rw [e2]; linarith
  · have := mul_le_mul_of_nonneg_left hE3 hc
    have e1 : 4 * ((z : ℝ) + 1) ^ 2 / (((eloq (-2 * z) : ℚ) : ℝ) * (z : ℝ) ^ 6) =
        4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * (1 / ((eloq (-2 * z) : ℚ) : ℝ)) := by
      field_simp
    have e2 : 4 * ((z : ℝ) + 1) ^ 2 * Real.exp (-(2 * (z : ℝ))) / (z : ℝ) ^ 6 =
        4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * Real.exp (-(2 * (z : ℝ))) := by ring
    rw [e1, e2]; linarith

/-- PROVED: a passing check gives `Δ > 0`, `Δ² > ε` and `1/(Δ² - ε) < n + 1` for `0 ≤ ε ≤ 10⁻⁸`. -/
theorem chk_sound (l0 L x : ℚ) (n : ℕ) (h : chk l0 L x n = true) (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 8) :
    4 * (l0 : ℝ) / 5 ≤ x ∧ 0 < Delta x L l0 ∧ ε < Delta x L l0 ^ 2 ∧
      1 / (Delta x L l0 ^ 2 - ε) < n + 1 := by
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hl0⟩, hlL⟩, h8a⟩, h8b⟩, hpa⟩, hpb⟩, hG1lo⟩, hnum⟩, hfin⟩ := h
  have hxpos : 0 < x := by linarith
  have hz2 : 0 < (L - l0) / x := div_pos (by linarith) hxpos
  have hz1 : -l0 / x < 0 := div_neg_of_neg_of_pos (by linarith) hxpos
  have g2 := G2lo_le _ hz2 h8a
  obtain ⟨g1l, g1h⟩ := G1_bounds _ hz1 h8b hpb
  have c2 : (((L - l0) / x : ℚ) : ℝ) = ((L : ℝ) - l0) / x := by push_cast; rfl
  have c1 : ((-l0 / x : ℚ) : ℝ) = -(l0 : ℝ) / x := by push_cast; rfl
  rw [c2] at g2; rw [c1] at g1l g1h
  set num : ℚ := G2lo ((L - l0) / x) - 8 / 45 * x with hnumdef
  set den : ℚ := G1hi (-l0 / x) with hdendef
  have hG1pos : (0 : ℝ) < Gz (-(l0 : ℝ) / x) := lt_of_lt_of_le (by exact_mod_cast hG1lo) g1l
  have hden : (0 : ℝ) < (den : ℝ) := lt_of_lt_of_le hG1pos g1h
  have hnum' : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnum
  have hnumle : (num : ℝ) ≤ Gz (((L : ℝ) - l0) / x) - 8 / 45 * (x : ℝ) := by
    rw [hnumdef]; push_cast; linarith
  have hD : Delta x L l0 = (Gz (((L : ℝ) - l0) / x) - 8 / 45 * (x : ℝ)) / Gz (-(l0 : ℝ) / x) := by
    unfold Delta; field_simp; ring
  have hDlo : (num : ℝ) / den ≤ Delta x L l0 := by
    rw [hD]
    calc (num : ℝ) / den ≤ (num : ℝ) / Gz (-(l0 : ℝ) / x) :=
          div_le_div_of_nonneg_left hnum'.le hG1pos g1h
      _ ≤ _ := div_le_div_of_nonneg_right hnumle hG1pos.le
  have hq : (0 : ℝ) < (num : ℝ) / den := div_pos hnum' hden
  have hDpos : 0 < Delta x L l0 := lt_of_lt_of_le hq hDlo
  have hsq : ((num : ℝ) / den) ^ 2 ≤ Delta x L l0 ^ 2 := pow_le_pow_left₀ hq.le hDlo 2
  have hfin' : (1 : ℝ) < ((n : ℝ) + 1) * (((num : ℝ) / den) ^ 2 - 1 / 10 ^ 8) := by
    have : ((1 : ℚ) : ℝ) < ((((n : ℚ) + 1) * (num ^ 2 / den ^ 2 - 1 / 10 ^ 8) : ℚ) : ℝ) := by
      exact_mod_cast hfin
    push_cast at this; rw [div_pow]; linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos : 0 < Delta x L l0 ^ 2 - ε := by
    by_contra hc; push Not at hc
    have : ((n : ℝ) + 1) * (((num : ℝ) / den) ^ 2 - 1 / 10 ^ 8) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hn1.le
      nlinarith
    linarith
  refine ⟨by exact_mod_cast hx, hDpos, by linarith, ?_⟩
  rw [div_lt_iff₀ hpos]
  nlinarith

/-! ### The grid -/

/-- The certified `xₖ` of gen/u6900_grid.py as numerator, denominator pairs, `k = 0, …, 200`. -/
def xs : List (ℕ × ℕ) := [(15481, 10000), (15529, 10000), (15577, 10000), (1953, 1250), (1567, 1000), (3143, 2000), (7879, 5000), (15801, 10000), (15843, 10000), (3971, 2500), (3981, 2500), (15963, 10000), (16001, 10000), (16039, 10000), (643, 400), (16111, 10000), (3229, 2000), (16179, 10000), (16213, 10000), (3249, 2000), (4069, 2500), (16307, 10000), (16337, 10000), (8183, 5000), (3279, 2000), (16423, 10000), (329, 200), (4119, 2500), (8251, 5000), (8263, 5000), (16551, 10000), (8287, 5000), (16597, 10000), (16619, 10000), (208, 125), (16661, 10000), (16681, 10000), (16701, 10000), (209, 125), (8369, 5000), (3351, 2000), (4193, 2500), (16789, 10000), (4201, 2500), (841, 500), (8417, 5000), (1053, 625), (16861, 10000), (8437, 5000), (8443, 5000), (8449, 5000), (16909, 10000), (16919, 10000), (16929, 10000), (16939, 10000), (4237, 2500), (4239, 2500), (4241, 2500), (16971, 10000), (8489, 5000), (2123, 1250), (16989, 10000), (8497, 5000), (16999, 10000), (17003, 10000), (17007, 10000), (1701, 1000), (4253, 2500), (8507, 5000), (2127, 1250), (17017, 10000), (8509, 5000), (8509, 5000), (17017, 10000), (2127, 1250), (3403, 2000), (17013, 10000), (17011, 10000), (1063, 625), (3401, 2000), (17001, 10000), (16997, 10000), (1062, 625), (16987, 10000), (16981, 10000), (679, 400), (16969, 10000), (8481, 5000), (8477, 5000), (8473, 5000), (8469, 5000), (16929, 10000), (423, 250), (1691, 1000), (169, 100), (16889, 10000), (8439, 5000), (16867, 10000), (3371, 2000), (16843, 10000), (1683, 1000), (16817, 10000), (16803, 10000), (16789, 10000), (671, 400), (419, 250), (2093, 1250), (2091, 1250), (2089, 1250), (2087, 1250), (16679, 10000), (16661, 10000), (16643, 10000), (133, 80), (8303, 5000), (16587, 10000), (16567, 10000), (16547, 10000), (8263, 5000), (8253, 5000), (4121, 2500), (8231, 5000), (411, 250), (8209, 5000), (3279, 2000), (16371, 10000), (16347, 10000), (16323, 10000), (8149, 5000), (16273, 10000), (16247, 10000), (16221, 10000), (3239, 2000), (2021, 1250), (16141, 10000), (16113, 10000), (3217, 2000), (2007, 1250), (16027, 10000), (7999, 5000), (998, 625), (7969, 5000), (15907, 10000), (3969, 2500), (3961, 2500), (3953, 2500), (789, 500), (15747, 10000), (15713, 10000), (196, 125), (3129, 2000), (15611, 10000), (1947, 1250), (777, 500), (969, 625), (3867, 2500), (15431, 10000), (15393, 10000), (3071, 2000), (15317, 10000), (7639, 5000), (15239, 10000), (15199, 10000), (15159, 10000), (15119, 10000), (7539, 5000), (3759, 2500), (7497, 5000), (1869, 1250), (14909, 10000), (2973, 2000), (14821, 10000), (14777, 10000), (3683, 2500), (7343, 5000), (183, 125), (7297, 5000), (14547, 10000), (29, 20), (3613, 2500), (14403, 10000), (7177, 5000), (2861, 2000), (2851, 2000), (3551, 2500), (14153, 10000), (14101, 10000), (14049, 10000), (3499, 2500), (13943, 10000), (13889, 10000), (6917, 5000), (13779, 10000), (3431, 2500), (13667, 10000), (13611, 10000), (13553, 10000), (2699, 2000), (13437, 10000), (13377, 10000), (6659, 5000)]

/-- The integer counts `n₀ = 6`, `n_{k+1} = nₖ + jumpsₖ`. -/
def cnt : ℕ → ℕ
  | 0 => 6
  | k + 1 => cnt k + jumps.getD k 0

/-- `Λₖ = 1.363 + k · 3.837/200` over `ℚ`. -/
def gridL (k : ℕ) : ℚ := 1363 / 1000 + k * (3837 / 200000)

/-- `xₖ` over `ℚ`. -/
def xq (k : ℕ) : ℚ := ((xs.getD k (1, 1)).1 : ℚ) / ((xs.getD k (1, 1)).2 : ℚ)

def gridOK : Bool := (List.range 201).all (fun k => chk (857 / 1000) (gridL k) (xq k) (cnt k))

set_option maxRecDepth 100000 in
/-- PROVED by kernel computation: all 201 checks pass. -/
theorem gridOK_true : gridOK = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cnt_200 : cnt 200 = 782 := by decide +kernel

/-- CONDITIONAL ON Zhao (3.26), Pintz's Theorem I, as the named hypothesis `h326` with its `ε`,
`0 ≤ ε ≤ 10⁻⁸`, for a nondecreasing or arbitrary count function `N`: at every grid point
`Λₖ = 1.363 + k · 3.837/200`, `k ≤ 200`, the integer count `N(Λₖ)` is at most `nₖ`. -/
theorem count_le_of_326 (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 8) (N : ℝ → ℕ)
    (h326 : ∀ L x : ℝ, 1.363 ≤ L → L ≤ 5.2 → 4 * 0.857 / 5 ≤ x → 0 < Delta x L 0.857 →
      ε < Delta x L 0.857 ^ 2 →
      (N L : ℝ) ≤ 1 / (Delta x L 0.857 ^ 2 - ε))
    (k : ℕ) (hk : k ≤ 200) : N (1.363 + k * (3.837 / 200)) ≤ cnt k := by
  have hall := gridOK_true
  unfold gridOK at hall
  rw [List.all_eq_true] at hall
  have hc := hall k (List.mem_range.mpr (by omega))
  obtain ⟨hx, hD, hε', hlt⟩ := chk_sound _ _ _ _ hc ε hε
  have eL : ((gridL k : ℚ) : ℝ) = 1.363 + k * (3.837 / 200) := by
    unfold gridL; push_cast; norm_num
  have e0 : ((857 / 1000 : ℚ) : ℝ) = 0.857 := by norm_num
  rw [eL, e0] at hε' hlt hD; rw [e0] at hx
  have hkr : (k : ℝ) ≤ 200 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have := h326 _ _ (by nlinarith) (by nlinarith) hx hD hε'
  have : (N (1.363 + k * (3.837 / 200)) : ℝ) < cnt k + 1 := lt_of_le_of_lt this hlt
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Vacuity: `N = 0` and `ε = 0` satisfy the hypothesis. -/
theorem count_vacuity : ∀ L x : ℝ, 1.363 ≤ L → L ≤ 5.2 → 4 * 0.857 / 5 ≤ x →
    0 < Delta x L 0.857 → (0 : ℝ) < Delta x L 0.857 ^ 2 → (((fun _ : ℝ => (0 : ℕ)) L : ℕ) : ℝ) ≤
      1 / (Delta x L 0.857 ^ 2 - 0) := by
  intro L x _ _ _ _ h; simp only [Nat.cast_zero, sub_zero]; positivity

end LeanLab.Zhao2025.U6900
