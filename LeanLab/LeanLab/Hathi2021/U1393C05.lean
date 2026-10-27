/-
U-1393, run 20261021T1003Z-20044. AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN.

Hathi, arXiv 2109.13174v3, Lemma 3.1 page 9 prints `c_{0,5} < 0.7773`; display 2.10 page 7
defines `c_{0,l} = 75/32 c_{1,l} + 105/32 c_{2,l}` with
`c_{1,l} = Σ μ²(d)/(c(d) β_l(3d))`, `c_{2,l} = Σ μ²(d)/(c(d) β_l(15d))`, `p ∣ d → p > 5`,
`β_l(d) = ρ(d)^{2l}/N_l(d)` by 2.8 and `N_l(d)` the count of display 2.7.

What is here, all from the definitions, no numerics trusted:
* `N_5(m)` for `m = 21, 33, 39, 51, 57, 105`, by kernel evaluation of the table `tab`
  proved equal to the count `cntF` in `FalsifierU6830`, together with `ρ(m)`.
* `invc p`, Hathi's `1/c(p)` from `1 + 1/c(p) = (1 + b(p)/(p-1)^4)/(1 + a(p)/(p-1)^4)`, page 5,
  evaluated at `p = 7, 11, 13, 17, 19`.
* `hathi_c05_ge_U1393`: eight terms of 2.10, `d = 1, 7, 11, 13, 17, 19` in `c_{1,5}` and
  `d = 1, 7` in `c_{2,5}`, give `c_{0,5} ≥ 1.0812` for any nonnegative summable families
  with those terms.
* `k31_fails_U1393`: so the section 4 criterion `0.9 > λ₀^{k'-10} · 11 · c_{0,5}`, display 4.3
  with `𝔍(0)/𝔍(1) → 1`, fails at `k' = 31`; with any valid `c_{0,5}` the argument of
  section 4 at `l = 5` cannot give `k' ≤ 31`, so not `k = 33` or less.
* `k32_ok_of`, `k33_ok_of`: the criterion holds at `k' = 32` for `c ≤ 1.219` and at `k' = 33`
  for `c ≤ 1.378`; the certified upper bound for `c_{0,5}` is Python only, see
  `numerics/U1393_c05_*.out`, TESTED, not PROVED here.
-/
import LeanLab.Hathi2021.FalsifierU6830

namespace LeanLab.Hathi2021.U1393C05

open Finset LeanLab.Hathi2021.FalsifierU6830

set_option maxHeartbeats 0

/-- `ρ(m) = r`: `2^r ≡ 1 mod m` and no smaller positive exponent works. -/
def IsOrd2 (m r : ℕ) : Prop := 2 ^ r % m = 1 ∧ ∀ k < r, 0 < k → 2 ^ k % m ≠ 1

instance (m r : ℕ) : Decidable (IsOrd2 m r) := by unfold IsOrd2; infer_instance

theorem rho21 : IsOrd2 21 6 := by decide
theorem rho33 : IsOrd2 33 10 := by decide
theorem rho39 : IsOrd2 39 12 := by decide
theorem rho51 : IsOrd2 51 8 := by decide
theorem rho57 : IsOrd2 57 18 := by decide
theorem rho105 : IsOrd2 105 12 := by decide

theorem tab21 : (tab 21 (wt 6) 5).getD 0 0 = 2894346 := by decide +kernel
theorem tab33 : (tab 33 (wt 10) 5).getD 0 0 = 303681510 := by decide +kernel
theorem tab39 : (tab 39 (wt 12) 5).getD 0 0 = 1590787092 := by decide +kernel
theorem tab51 : (tab 51 (wt 8) 5).getD 0 0 = 21123368 := by decide +kernel
theorem tab57 : (tab 57 (wt 18) 5).getD 0 0 = 62762807718 := by decide +kernel
theorem tab105 : (tab 105 (wt 12) 5).getD 0 0 = 597386244 := by decide +kernel

theorem N5_21 : cntF 5 21 (wt 6) 0 = 2894346 := by
  have h := cntF_eq_tab 21 (by norm_num) (wt 6) 5 0
  simp only [Nat.cast_ofNat] at h; exact h.trans tab21
theorem N5_33 : cntF 5 33 (wt 10) 0 = 303681510 := by
  have h := cntF_eq_tab 33 (by norm_num) (wt 10) 5 0
  simp only [Nat.cast_ofNat] at h; exact h.trans tab33
theorem N5_39 : cntF 5 39 (wt 12) 0 = 1590787092 := by
  have h := cntF_eq_tab 39 (by norm_num) (wt 12) 5 0
  simp only [Nat.cast_ofNat] at h; exact h.trans tab39
theorem N5_51 : cntF 5 51 (wt 8) 0 = 21123368 := by
  have h := cntF_eq_tab 51 (by norm_num) (wt 8) 5 0
  simp only [Nat.cast_ofNat] at h; exact h.trans tab51
theorem N5_57 : cntF 5 57 (wt 18) 0 = 62762807718 := by
  have h := cntF_eq_tab 57 (by norm_num) (wt 18) 5 0
  simp only [Nat.cast_ofNat] at h; exact h.trans tab57
theorem N5_105 : cntF 5 105 (wt 12) 0 = 597386244 := by
  have h := cntF_eq_tab 105 (by norm_num) (wt 12) 5 0
  simp only [Nat.cast_ofNat] at h; exact h.trans tab105

/-- Hathi's `a(p)`, page 5. -/
def aP (p : ℕ) : ℚ := if p % 4 = 3 then -((p : ℚ) + 1) ^ 2 else 3 * (p : ℚ) ^ 2 - 2 * p - 1
/-- Hathi's `b(p)`, page 5. -/
def bP (p : ℕ) : ℚ :=
  if p % 4 = 3 then ((p : ℚ) - 1) * ((p : ℚ) + 1) ^ 2 else ((p : ℚ) - 1) * ((p : ℚ) ^ 2 + 6 * p + 1)
/-- `1/c(p)` from `1 + 1/c(p) = (1 + b(p)/(p-1)^4)/(1 + a(p)/(p-1)^4)`, page 5. -/
def invc (p : ℕ) : ℚ := (1 + bP p / ((p : ℚ) - 1) ^ 4) / (1 + aP p / ((p : ℚ) - 1) ^ 4) - 1

theorem invc7 : invc 7 = 4 / 11 := by norm_num [invc, aP, bP]
theorem invc11 : invc 11 = 9 / 56 := by norm_num [invc, aP, bP]
theorem invc13 : invc 13 = 2 / 17 := by norm_num [invc, aP, bP]
theorem invc17 : invc 17 = 5 / 61 := by norm_num [invc, aP, bP]
theorem invc19 : invc 19 = 25 / 344 := by norm_num [invc, aP, bP]

/-- Eight terms of display 2.10 at `l = 5`. `f d` stands for `μ²(d)/(c(d) β₅(3d))` and
`g d` for `μ²(d)/(c(d) β₅(15d))`, with `1/β₅(m) = N₅(m)/ρ(m)^10` by 2.8. -/
theorem hathi_c05_ge_U1393 (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ d, 0 ≤ f d) (hg0 : ∀ d, 0 ≤ g d)
    (hf1 : f 1 = (cntF 5 3 (wt 2) 0 : ℝ) / 2 ^ 10)
    (hf7 : f 7 = (invc 7 : ℝ) * ((cntF 5 21 (wt 6) 0 : ℝ) / 6 ^ 10))
    (hf11 : f 11 = (invc 11 : ℝ) * ((cntF 5 33 (wt 10) 0 : ℝ) / 10 ^ 10))
    (hf13 : f 13 = (invc 13 : ℝ) * ((cntF 5 39 (wt 12) 0 : ℝ) / 12 ^ 10))
    (hf17 : f 17 = (invc 17 : ℝ) * ((cntF 5 51 (wt 8) 0 : ℝ) / 8 ^ 10))
    (hf19 : f 19 = (invc 19 : ℝ) * ((cntF 5 57 (wt 18) 0 : ℝ) / 18 ^ 10))
    (hg1 : g 1 = (cntF 5 15 (wt 4) 0 : ℝ) / 4 ^ 10)
    (hg7 : g 7 = (invc 7 : ℝ) * ((cntF 5 105 (wt 12) 0 : ℝ) / 12 ^ 10)) :
    (10812 / 10000 : ℝ) ≤ 75 / 32 * (∑' d, f d) + 105 / 32 * (∑' d, g d) := by
  have a : f 1 + (f 7 + (f 11 + (f 13 + (f 17 + f 19)))) ≤ ∑' d, f d := by
    have := hf.sum_le_tsum ({1, 7, 11, 13, 17, 19} : Finset ℕ) (fun j _ => hf0 j)
    simpa [Finset.sum_insert, Finset.sum_singleton] using this
  have b : g 1 + g 7 ≤ ∑' d, g d := by
    have := hg.sum_le_tsum ({1, 7} : Finset ℕ) (fun j _ => hg0 j)
    simpa [Finset.sum_insert, Finset.sum_singleton] using this
  rw [hf1, hf7, hf11, hf13, hf17, hf19, N5_3, N5_21, N5_33, N5_39, N5_51, N5_57,
    invc7, invc11, invc13, invc17, invc19] at a
  rw [hg1, hg7, N5_15, N5_105, invc7] at b
  norm_num at a b
  nlinarith

/-- `λ₀ = 0.8844473`, page 13, from Platt and Trudgian. -/
noncomputable def lam : ℝ := 8844473 / 10000000

/-- Section 4 criterion at `l = 5`, `k' = 31`: fails for every `c ≥ 1.0812`. -/
theorem k31_fails_of (c : ℝ) (hc : 10812 / 10000 ≤ c) : 9 / 10 - lam ^ (31 - 2 * 5) * 11 * c < 0 := by
  have h : 9 / 10 - lam ^ (31 - 2 * 5) * 11 * (10812 / 10000) < 0 := by unfold lam; norm_num
  have : 0 ≤ lam ^ (31 - 2 * 5) * 11 := by unfold lam; positivity
  nlinarith [mul_le_mul_of_nonneg_left hc this]

/-- Under the hypotheses of `hathi_c05_ge_U1393`, i.e. with Hathi's own `c_{0,5}` of 2.10,
the section 4 criterion fails at `k' = 31`. -/
theorem k31_fails_U1393 (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ d, 0 ≤ f d) (hg0 : ∀ d, 0 ≤ g d)
    (hf1 : f 1 = (cntF 5 3 (wt 2) 0 : ℝ) / 2 ^ 10)
    (hf7 : f 7 = (invc 7 : ℝ) * ((cntF 5 21 (wt 6) 0 : ℝ) / 6 ^ 10))
    (hf11 : f 11 = (invc 11 : ℝ) * ((cntF 5 33 (wt 10) 0 : ℝ) / 10 ^ 10))
    (hf13 : f 13 = (invc 13 : ℝ) * ((cntF 5 39 (wt 12) 0 : ℝ) / 12 ^ 10))
    (hf17 : f 17 = (invc 17 : ℝ) * ((cntF 5 51 (wt 8) 0 : ℝ) / 8 ^ 10))
    (hf19 : f 19 = (invc 19 : ℝ) * ((cntF 5 57 (wt 18) 0 : ℝ) / 18 ^ 10))
    (hg1 : g 1 = (cntF 5 15 (wt 4) 0 : ℝ) / 4 ^ 10)
    (hg7 : g 7 = (invc 7 : ℝ) * ((cntF 5 105 (wt 12) 0 : ℝ) / 12 ^ 10)) :
    9 / 10 - lam ^ (31 - 2 * 5) * 11 * (75 / 32 * (∑' d, f d) + 105 / 32 * (∑' d, g d)) < 0 :=
  k31_fails_of _ (hathi_c05_ge_U1393 f g hf hg hf0 hg0 hf1 hf7 hf11 hf13 hf17 hf19 hg1 hg7)

/-- The criterion holds at `k' = 32` for every `c ≤ 1.219`. -/
theorem k32_ok_of (c : ℝ) (hc : c ≤ 1219 / 1000) : 0 < 9 / 10 - lam ^ (32 - 2 * 5) * 11 * c := by
  have h : 0 < 9 / 10 - lam ^ (32 - 2 * 5) * 11 * (1219 / 1000) := by unfold lam; norm_num
  have : 0 ≤ lam ^ (32 - 2 * 5) * 11 := by unfold lam; positivity
  nlinarith [mul_le_mul_of_nonneg_left hc this]

/-- The criterion holds at `k' = 33` for every `c ≤ 1.378`. -/
theorem k33_ok_of (c : ℝ) (hc : c ≤ 1378 / 1000) : 0 < 9 / 10 - lam ^ (33 - 2 * 5) * 11 * c := by
  have h : 0 < 9 / 10 - lam ^ (33 - 2 * 5) * 11 * (1378 / 1000) := by unfold lam; norm_num
  have : 0 ≤ lam ^ (33 - 2 * 5) * 11 := by unfold lam; positivity
  nlinarith [mul_le_mul_of_nonneg_left hc this]

/-- P0101 page 197 and P0102 page 88 print `S²(h) ≤ 8.54 κ²(h) ∏ …`, with `8.54` standing for
`9 c₄²`. For any `c₄ ≥ 0.97422`, which is `C4Lower.c4_ge_97422`, PROVED in the lab but not
imported here to avoid rebuilding the C4 chain, `9 c₄² > 8.54`: the printed constant is rounded
down, by at least `0.0019`. -/
theorem nine_c4sq_gt (c : ℝ) (hc : 97422 / 100000 ≤ c) : 854 / 100 + 19 / 10000 < 9 * c ^ 2 := by
  nlinarith

/-- The printed bound is below the proved lower bound. -/
theorem printed_lt_U1393 : (7773 / 10000 : ℝ) < 10812 / 10000 := by norm_num

end LeanLab.Hathi2021.U1393C05
