import Mathlib
import LeanLab.HelfgottMajor.BookT143Range

/-!
# Helfgott's book, Part IV of 2020-04-01, Theorem 14.3: the exponential term for all `r > 0`

Unit U-1428, PC run 20261021T1303Z-13145, P0014. AI wrote this file.

`E` is `BookE.E`, the function of (15.2) of the book. In the proofs of Theorem 14.3 on book
pp. 448 to 451, `T₀ = K max(|δ|, 4)` with `K = 1375/32` in part 1, `K = 125/2` in part 2, and
the exponential term is `max(1.05, 2.72/√r) e^{-E(r) T₀}` where `T₀ = K²/(π² r)` when
`|δ| ≥ 4`, that is `r ≤ r₀ = K/(4π²)`, and `T₀ = 4K` when `r ≥ r₀`. So the two branches are
* `r ≤ r₀`: `max(1.05, 2.72/√r) e^{-E(r)/(rπ²)·K²}`, the term of `BookT143Range`;
* `r ≥ r₀`: `max(1.05, 2.72/√r) e^{-E(r)·4K}`, `4K = 1375/8`, resp. `250`; at `r = r₀` the two
  exponents agree, `BookT143.r0_p1`, `BookT143.r0_p2`.

Method for `r ≥ r₀`, monotonicity: `E` is non-decreasing on `r > 0`, since `E(R(t)) = F(t)` with
`F' = (1 + 6t² + t⁴)/(2(1 + t²)²) > 0` and `R` increasing, the tools of BookL1523; and
`max(1.05, 2.72/√r)` is non-increasing. So the `r ≥ r₀` branch is non-increasing on `[r₀, ∞)`
and bounded by its value at `r₀`, which is `lead_p1_E`, `lead_p2_E` of BookE. Python, scratch
u1428_check.py, 30 digits, a 4001 point log grid on `[r₀, 10¹⁰ r₀]`: `E` increasing, the term
decreasing, maxima 1.5929817·10⁻⁹ and 1.8018503·10⁻¹⁸ at `r₀`.

PROVED:
* `Ft_mono`, `E_mono`: `E` is monotone on `r > 0`;
* `inv_sqrt_r0_p1`, `inv_sqrt_r0_p2`: `1/√r₀ = π√(128/1375)`, resp. `π√(8/125)`;
* `upper_antitone`: the `r ≥ r₀` branch, for any `c ≥ 0`, is non-increasing in `r > 0`;
* `upper_p1`, `upper_p2`: for every `r ≥ r₀` the `r ≥ r₀` branch is at most `1.59299·10⁻⁹`,
  resp. `1.80186·10⁻¹⁸`, the printed constants, and at most its value at `r₀`;
* `termP1`, `termP2`: the piecewise term; `all_p1`: `termP1 r ≤ 1.15275·10⁻⁷` for every `r > 0`
  with the book's cap `1/√r ≤ 606.225`, and `all_p1_mid`: `≤ 6.02·10⁻⁹` for `r ≥ 0.001`;
  `all_p2`: `termP2 r ≤ 1.80186·10⁻¹⁸` for every `r > 0` with `1/√r ≤ 584.033`.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN. AI-written Lean code,
Claude, 2026-10-21.
-/

namespace LeanLab.HelfgottMajor.BookT143All
open Real Set
open LeanLab.HelfgottMajor.BookE LeanLab.HelfgottMajor.BookL1523
  LeanLab.HelfgottMajor.BookT143Range

/-- `F(t) = arctan t - g(t)` is monotone, `F' = (1 + 6t² + t⁴)/(2(1 + t²)²) ≥ 0`. -/
theorem Ft_mono : Monotone Ft := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_Ft x).differentiableAt)
  intro x
  rw [(hasDerivAt_Ft x).deriv]
  positivity

/-- **`E` is non-decreasing on `r > 0`.** -/
theorem E_mono : MonotoneOn E (Ioi 0) := by
  intro a ha b hb hab
  obtain ⟨ta, hta, hRa⟩ := Rt_surj (r := a) ha
  obtain ⟨tb, htb, hRb⟩ := Rt_surj (r := b) hb
  have hle : ta ≤ tb := by
    by_contra h
    push Not at h
    have := Rt_strictMono ⟨htb.1.le, htb.2⟩ ⟨hta.1.le, hta.2⟩ h
    rw [hRa, hRb] at this
    linarith
  rw [← hRa, ← hRb, E_Rt hta.1 hta.2, E_Rt htb.1 htb.2]
  exact Ft_mono hle

/-- `1/√(a/(bπ²)) = π√(b/a)`. -/
lemma inv_sqrt_r0 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / √(a / (b * π ^ 2)) = π * √(b / a) := by
  have hp : 0 < π := pi_pos
  rw [one_div, ← sqrt_inv, inv_div]
  rw [show b * π ^ 2 / a = (π * √(b / a)) ^ 2 by
    rw [mul_pow, sq_sqrt (by positivity)]; field_simp]
  exact sqrt_sq (by positivity)

lemma inv_sqrt_r0_p1 : 1 / √(1375 / (128 * π ^ 2)) = π * √(128 / 1375) :=
  inv_sqrt_r0 (by norm_num) (by norm_num)

lemma inv_sqrt_r0_p2 : 1 / √(125 / (8 * π ^ 2)) = π * √(8 / 125) :=
  inv_sqrt_r0 (by norm_num) (by norm_num)

/-- **The `r ≥ r₀` branch is non-increasing**: for `0 < a ≤ b` and `c ≥ 0`,
`max(1.05, 2.72/√b) e^{-E(b)c} ≤ max(1.05, 2.72/√a) e^{-E(a)c}`. -/
theorem upper_antitone {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c) :
    max 1.05 (2.72 * (1 / √b)) * exp (-(E b * c)) ≤
      max 1.05 (2.72 * (1 / √a)) * exp (-(E a * c)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hE : E a ≤ E b := E_mono (show a ∈ Ioi (0 : ℝ) from ha) (show b ∈ Ioi (0 : ℝ) from hb) hab
  have hs : 1 / √b ≤ 1 / √a :=
    one_div_le_one_div_of_le (sqrt_pos.mpr ha) (sqrt_le_sqrt hab)
  have hm : max 1.05 (2.72 * (1 / √b)) ≤ max 1.05 (2.72 * (1 / √a)) :=
    max_le_max le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hx : exp (-(E b * c)) ≤ exp (-(E a * c)) :=
    exp_le_exp.mpr (by nlinarith)
  exact mul_le_mul hm hx (exp_pos _).le (le_max_of_le_left (by norm_num))

/-- **Part 1, `r ≥ r₀`**: `max(1.05, 2.72/√r) e^{-E(r)·1375/8}` is at most its value at
`r₀ = 1375/(128π²)` and at most `1.59299·10⁻⁹`, book p. 449. -/
theorem upper_p1 {r : ℝ} (h : 1375 / (128 * π ^ 2) ≤ r) :
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r * (1375 / 8))) ≤
      max 1.05 (2.72 * (1 / √(1375 / (128 * π ^ 2)))) *
        exp (-(E (1375 / (128 * π ^ 2)) * (1375 / 8))) ∧
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r * (1375 / 8))) ≤ 1.59299e-9 := by
  have hr0 : (0 : ℝ) < 1375 / (128 * π ^ 2) := by positivity
  have h1 := upper_antitone hr0 h (c := 1375 / 8) (by norm_num)
  refine ⟨h1, h1.trans ?_⟩
  rw [inv_sqrt_r0_p1, max_eq_right (BookT143.lead_p1 E_p1).1]
  have := lead_p1_E
  rw [show -(E (1375 / (128 * π ^ 2)) * 1375 / 8) = -(E (1375 / (128 * π ^ 2)) * (1375 / 8))
    by ring] at this
  exact this

/-- **Part 2, `r ≥ r₀`**: `max(1.05, 2.72/√r) e^{-250 E(r)}` is at most its value at
`r₀ = 125/(8π²)` and at most `1.80186·10⁻¹⁸`, book p. 450. -/
theorem upper_p2 {r : ℝ} (h : 125 / (8 * π ^ 2) ≤ r) :
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r * 250)) ≤
      max 1.05 (2.72 * (1 / √(125 / (8 * π ^ 2)))) * exp (-(E (125 / (8 * π ^ 2)) * 250)) ∧
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r * 250)) ≤ 1.80186e-18 := by
  have hr0 : (0 : ℝ) < 125 / (8 * π ^ 2) := by positivity
  have h1 := upper_antitone hr0 h (c := 250) (by norm_num)
  refine ⟨h1, h1.trans ?_⟩
  rw [inv_sqrt_r0_p2, max_eq_right (BookT143.lead_p2 E_c4).1]
  exact lead_p2_E

/-! ## The piecewise term for all `r > 0` -/

/-- The part 1 term: exponent `E(r)/(rπ²)·(1375/32)²` for `r ≤ r₀`, `E(r)·1375/8` for `r > r₀`. -/
noncomputable def termP1 (r : ℝ) : ℝ :=
  if r ≤ 1375 / (128 * π ^ 2) then
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2))
  else max 1.05 (2.72 * (1 / √r)) * exp (-(E r * (1375 / 8)))

/-- The part 2 term: exponent `E(r)/(rπ²)·(125/2)²` for `r ≤ r₀`, `250 E(r)` for `r > r₀`. -/
noncomputable def termP2 (r : ℝ) : ℝ :=
  if r ≤ 125 / (8 * π ^ 2) then
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2))
  else max 1.05 (2.72 * (1 / √r)) * exp (-(E r * 250))

/-- **Theorem 14.3 part 1, all `r > 0`**, with the book's cap `1/√r ≤ 606.225`:
`termP1 r ≤ 1.15275·10⁻⁷`, the value of p. 449 that gives `ε₊`. -/
theorem all_p1 {r : ℝ} (h0 : 0 < r) (hs : 1 / √r ≤ 606.225) : termP1 r ≤ 1.15275e-7 := by
  unfold termP1
  split_ifs with h
  · exact range_p1 h0 h hs
  · exact (upper_p1 (le_of_not_ge h)).2.trans (by norm_num)

/-- **Part 1 for `r ≥ 0.001`**: `termP1 r ≤ 6.02·10⁻⁹`. -/
theorem all_p1_mid {r : ℝ} (h1 : 0.001 ≤ r) : termP1 r ≤ 6.02e-9 := by
  unfold termP1
  split_ifs with h
  · exact range_p1_mid h1 h
  · exact (upper_p1 (le_of_not_ge h)).2.trans (by norm_num)

/-- **Theorem 14.3 part 2, all `r > 0`**, with the book's cap `1/√r ≤ 584.033`:
`termP2 r ≤ 1.80186·10⁻¹⁸ ≤ 1.8019·10⁻¹⁸`, the printed bisection value of p. 450. -/
theorem all_p2 {r : ℝ} (h0 : 0 < r) (hs : 1 / √r ≤ 584.033) : termP2 r ≤ 1.80186e-18 := by
  unfold termP2
  split_ifs with h
  · exact range_p2 h0 h hs
  · exact (upper_p2 (le_of_not_ge h)).2

end LeanLab.HelfgottMajor.BookT143All
