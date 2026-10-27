/-
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Prop. 4.12 for
`η₊²`, pages 52 to 54, U-6067, CLOUD 20261020T0516Z-cloud35.

FINDING F-5033, cosmetic, superseded: (4.72) prints `0.40742 · (0.80044 log x + 0.82999) ≤ 0.32396 log x
+ 0.33592`, but the product is `0.32612 log x + 0.33815`, `eq472_fails`. With the product, (4.75) is
not at most `2.06 log x √T₀ log T₀ + 43.866 log x` at `x = 10⁸`, `T₀ = 150`, which Prop. 4.12 allows,
`bound206_fails_150`; it holds from about `T₀ = 161`. The book version 1501.05438 redoes the section
with `H ≥ 25`, `T₀ ≥ 200`, its (9.78) `0.4976 · (0.80365 log x + 0.82999) ≤ 0.3999 log x + 0.41301`
is right, `book_978`. Also (4.71)'s `18.593 log x` reappears as `18.539 log x` on p. 54, a typo.

The `ℓ∞` bounds (B.38) and (B.40) at `H = 50` are checked: `sup_bounds`.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.HelfgottMajor.Sec48

namespace LeanLab.HelfgottMajor.Prop412
open Real

/-- `(1 + (4/π) log H)/H` at `H = 50` lies in `[0.119618, 0.11962]`. -/
lemma f50 : 0.119618 ≤ (1 + 4 / π * log 50) / 50 ∧ (1 + 4 / π * log 50) / 50 ≤ 0.11962 := by
  have hp := pi_gt_d20; have hp' := pi_lt_d20
  have hl : log 50 = 2 * log 10 - log 2 := by
    rw [show (50 : ℝ) = 10 ^ 2 / 2 by norm_num, log_div (by norm_num) (by norm_num), log_pow]; norm_num
  have h10 := log_ten_gt; have h10' := log_ten_lt; have h2 := log_two_gt_d9; have h2' := log_two_lt_d9
  have hlo : 3.912022 < log 50 := by rw [hl]; linarith
  have hhi : log 50 < 3.912024 := by rw [hl]; linarith
  have q1 : 4 / π * log 50 ≤ 4 / 3.14159265358979323846 * 3.912024 := by
    apply mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le) hhi.le
      (by linarith) (by norm_num)
  have q2 : 4 / 3.14159265358979323847 * 3.912022 ≤ 4 / π * log 50 := by
    apply mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp'.le) hlo.le
      (by norm_num) (by positivity)
  constructor
  · rw [le_div_iff₀ (by norm_num)]; norm_num at q2 ⊢; linarith
  · rw [div_le_iff₀ (by norm_num)]; norm_num at q1 ⊢; linarith

/-- **(B.38), (B.40) at `H = 50`: `|η₊|∞ ≤ 1.246945`, `|η₊ log t|∞ ≤ 0.40742`**, MATCH, 1.2469420 and
0.4074181. -/
theorem sup_bounds : 1 + 2.06440727 * ((1 + 4 / π * log 50) / 50) ≤ 1.246945 ∧
    0.279491 + 1.069456 * ((1 + 4 / π * log 50) / 50) ≤ 0.40742 := by
  have := f50.2; constructor <;> nlinarith

/-- **(4.72) does not follow**: `0.40742 · 0.80044 > 0.32396` and `0.40742 · 0.82999 > 0.33592`. -/
theorem eq472_fails : (0.32396 : ℝ) < 0.40742 * 0.80044 ∧ (0.33592 : ℝ) < 0.40742 * 0.82999 := by
  constructor <;> norm_num

/-- **The book's (9.78) is right**: `0.4976 · 0.80365 ≤ 0.3999`, `0.4976 · 0.82999 ≤ 0.41301`. -/
theorem book_978 : (0.4976 : ℝ) * 0.80365 ≤ 0.3999 ∧ (0.4976 : ℝ) * 0.82999 ≤ 0.41301 := by
  constructor <;> norm_num

/-- **With the products of (4.72), (4.75) exceeds `2.06 log x √T₀ log T₀ + 43.866 log x` at
`x = 10⁸`, `T₀ = 150`**: the coefficients `(|η₊,₂|₂ + |η₊,₂ log|₂)`, `17.21 |η₊,₂ log|₂ − log(2π√e)|η₊,₂|₂`
from (4.73) and the true (4.72), `L = log x = 8 log 10`. -/
theorem bound206_fails_150 :
    let L := 8 * log 10
    let a1 := 0.40742 * 0.80044; let a0 := 0.40742 * 0.82999
    2.06 * L * √150 * log 150 + 43.866 * L <
      ((a1 + 0.99811) * L + (a0 + 0.32612)) * √150 * log 150 +
        ((17.21 * a1 - log (2 * π * √(exp 1)) * 0.99811) * L +
          (17.21 * a0 - log (2 * π * √(exp 1)) * 0.32612)) * √150 + 43.1 * L + 14.1 := by
  intro L a1 a0
  have h10 := log_ten_gt; have h10' := log_ten_lt
  have hl := LeanLab.HelfgottMajor.Sec48.log_two_pi_sqrt_e
  have hs : 12.2474 < √150 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs' : √150 < 12.2475 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have he := exp_one_gt_d9
  have he5 : (148.4131 : ℝ) ≤ exp 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) * 1 by norm_num, exp_nat_mul]
    have := pow_le_pow_left₀ (by norm_num) he.le 5
    norm_num at this ⊢; linarith
  have hg : log 150 ≤ 5.0107 := by
    have h1 : log 150 = 5 + log (150 / exp 5) := by
      rw [log_div (by norm_num) (exp_pos 5).ne', log_exp]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < 150 / exp 5 by positivity)
    have h3 : 150 / exp 5 ≤ 150 / 148.4131 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he5
    rw [h1]; norm_num at h3; linarith
  have hg0 : 5 ≤ log 150 := by
    rw [show (5 : ℝ) = log (exp 5) by rw [log_exp]]
    apply log_le_log (exp_pos 5)
    have := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    have h5 : exp 5 = exp 1 ^ 5 := by rw [← exp_nat_mul]; norm_num
    have he' := exp_one_lt_d9
    rw [h5]; nlinarith [pow_le_pow_left₀ (exp_pos 1).le he'.le 5]
  set g := log 150
  set s := √150
  set lam := log (2 * π * √(exp 1))
  have hL1 : L ≤ 18.4206832 := by simp only [L]; linarith
  have hL0 : 18.42 ≤ L := by simp only [L]; linarith
  have hlam := hl.2
  have hA : 0.86 ≤ ((a1 + 0.99811) * L + (a0 + 0.32612) - 2.06 * L) * g +
      ((17.21 * a1 - lam * 0.99811) * L + (17.21 * a0 - lam * 0.32612)) := by
    simp only [a1, a0]
    nlinarith [mul_le_mul hL1 hg (by linarith) (by linarith), mul_nonneg (by linarith : (0 : ℝ) ≤ 18.4206832 - L) (by linarith : (0 : ℝ) ≤ 5.0107 - g),
      mul_le_mul_of_nonneg_left hlam.le (by linarith : (0 : ℝ) ≤ L)]
  have key : 2.06 * L * s * g + 0.86 * s ≤
      ((a1 + 0.99811) * L + (a0 + 0.32612)) * s * g +
        ((17.21 * a1 - lam * 0.99811) * L + (17.21 * a0 - lam * 0.32612)) * s := by
    have := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ s)
    linarith
  linarith


/-- **(4.73)**: `|η₊|∞ |η₊|₂ ≤ 0.99811` and `|η₊ log t|∞ |η₊|₂ ≤ 0.32612` with (B.38), (B.40), (B.25),
MATCH, 0.9981022 and 0.3261138. -/
theorem eq473 : (1.246945 : ℝ) * 0.80044 ≤ 0.99811 ∧ (0.40742 : ℝ) * 0.80044 ≤ 0.32612 := by
  constructor <;> norm_num

/-- **(4.74)**: `(|η₊|∞ log x + |η₊ log t|∞) |η₊/√t|₁ ≤ 1.24703 log x + 0.40745` with
`|η₊/√t|₁ ≤ 1.062319 √Γ(3/2) ≤ 1.0000647`, MATCH, 1.2470218 and 0.4074443. -/
theorem eq474 : 1.062319 * √LeanLab.HelfgottMajor.Sec45.nTwo ≤ (1.0000647 : ℝ) ∧
    (1.246945 : ℝ) * 1.0000647 ≤ 1.24703 ∧ (0.40742 : ℝ) * 1.0000647 ≤ 0.40745 := by
  have h := LeanLab.HelfgottMajor.Sec45.sqrt_nTwo_lt
  refine ⟨by nlinarith, by norm_num, by norm_num⟩

/-- **(4.71)**: `c₀ + (162.56 log x + 59.325) x^{-1/2} ≤ 18.593 log x` with
`c₀ ≤ 18.15014 log x + 7.84532` and `x ≥ 10⁸`, MATCH, 18.59263 at `x = 10⁸`; p. 54 repeats it as
18.539, a typo. -/
theorem eq471 {x : ℝ} (hx : 1e8 ≤ x) :
    18.15014 * log x + 7.84532 + (162.56 * log x + 59.325) / √x ≤ 18.593 * log x := by
  have hlx : 18.420678 ≤ log x := by
    have := log_le_log (by norm_num) hx
    have h8 : log (1e8 : ℝ) = 8 * log 10 := by
      rw [show (1e8 : ℝ) = 10 ^ 8 by norm_num, log_pow]; norm_num
    have := log_ten_gt; linarith
  have hs : 10000 ≤ √x := by rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hs0 : 0 < √x := by linarith
  have h1 : (162.56 * log x + 59.325) / √x ≤ (162.56 * log x + 59.325) / 10000 :=
    div_le_div_of_nonneg_left (by nlinarith) (by norm_num) hs
  linarith

end LeanLab.HelfgottMajor.Prop412
