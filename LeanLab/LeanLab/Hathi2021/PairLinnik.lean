/-
U-6827, I-5160, CLOUD 20261020T2317Z-cloud53. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

P0101 L. Hu, A pair of equations in one prime, two prime squares and powers of 2,
Acta Arith. 191 2019, 191-200, K = 82.
P0102 L. Hu, Y. Kong, Z. Liu, A pair of equations in four prime squares and powers of 2,
Ramanujan J. 54 2021, 79-92, k = 98.

Both papers bound the minor arc by Cauchy-Schwarz with a mean value of
`T⁴(α₁) T⁴(α₂) G²⁸(α₁ + α₂)`, whose arithmetic part is `Σ_{h ≠ 0} r₁₄(h) 𝔖(h)²`, a squared
singular series with fourteen pairs of powers of 2. Both print the bound `23.39 L²⁸`.
Hathi's Lemma 3.1 bounds `Σ_{h ≠ 0} r_l(h) 𝔖(h)` with the first power of `𝔖` and
`1 ≤ l ≤ 8`. So it does not apply to either paper: different sum, different power of the
singular series, different `l`. No substitution is made below.

What is here, every analytic input a named hypothesis or a stated real number:
* `margin101`, `margin102`: the closing inequalities, reproduced and shown tight.
* `p0101_unrounded`: P0101 rounds `128² · 23.39 = 383221.76` down to `3.83 · 10⁵`; with the
  unrounded value K = 82 still holds.
* the local factor at `p = 5`, `5 ∣ h`, is `15/8`, from each paper's own table of `B(p, h)`;
  both papers use `κ = 3/2` there. `coeff_corrected` gives `22.93` in place of `14.0026`.
* `p0101_worst`, `p0102_worst`: if `Σ r₁₄ 𝔖² ≤ 33.3 L²⁸`, then K = 84 and k = 101 hold.
* `hathi_c01_gt`, `hathi_c05_gt`: Hathi's `c_{0,l}` as defined in his display 2.10 is above
  his printed Lemma 3.1 bounds at `l = 1` and `l = 5`, from the `d = 1` term alone.
-/
import Mathlib

namespace LeanLab.Hathi2021.PairLinnik

open Real Finset

/-- `λ = 0.8844473`, Platt-Trudgian, used by both papers. -/
def lam : ℚ := 8844473 / 10000000

/-! ### P0101, page 199 -/

/-- P0101 closing inequality, page 199: `5.56388 π²/16 - C λ^{k-16}`, with `C = 10823.8`
printed. Positivity for `N₁N₂Lᵏ` gives `R(N₁, N₂) > 0`. -/
noncomputable def margin101 (C : ℝ) (k : ℕ) : ℝ :=
  556388 / 100000 * π ^ 2 / 16 - C * (lam : ℝ) ^ (k - 16)

theorem pi_sq_bounds : (3141592 / 1000000 : ℝ) ^ 2 < π ^ 2 ∧ π ^ 2 < (3141593 / 1000000 : ℝ) ^ 2 := by
  have h1 := Real.pi_gt_d6; have h2 := Real.pi_lt_d6
  constructor
  · exact pow_lt_pow_left₀ (by norm_num at h1 ⊢; linarith) (by norm_num) (by norm_num)
  · have h2' : π < (3141593 / 1000000 : ℝ) := by norm_num at h2 ⊢; linarith
    exact pow_lt_pow_left₀ h2' Real.pi_pos.le two_ne_zero

/-- P0101 Theorem 1.1, K = 82, reproduced from the printed constant 10823.8, and tight:
K = 81 fails. -/
theorem p0101_reproduced : 0 < margin101 (108238 / 10) 82 ∧ margin101 (108238 / 10) 81 < 0 := by
  obtain ⟨h1, h2⟩ := pi_sq_bounds
  unfold margin101 lam
  constructor
  · norm_num at h1 ⊢; nlinarith
  · norm_num at h2 ⊢; nlinarith

/-- `10823.8 = √(305.8869 · 3.83·10⁵)` to the printed digit: the product lies between
`10823.75²` and `10823.85²`. -/
theorem p0101_C_printed :
    (1082375 / 100 : ℚ) ^ 2 < 3058869 / 10000 * 383000 ∧
      3058869 / 10000 * 383000 < (1082385 / 100 : ℚ) ^ 2 := by norm_num

/-- The rounding: `128² · 23.39 = 383221.76 > 3.83 · 10⁵`, so the printed `I` bound on
page 199 is rounded down. -/
theorem p0101_rounding : (128 : ℚ) ^ 2 * (2339 / 100) = 38322176 / 100 ∧
    (383000 : ℚ) < 128 ^ 2 * (2339 / 100) := by norm_num

/-- Squared form of the P0101 criterion with the unrounded constant: for `A > 0`,
`A > √X λⁿ` iff `A² > X λ²ⁿ`. Here `A = 5.56388 π²/16`, `X = 305.8869 · 128² · D`. -/
noncomputable def sq101 (D : ℝ) (k : ℕ) : ℝ :=
  (556388 / 100000 * π ^ 2 / 16) ^ 2 - 3058869 / 10000 * 128 ^ 2 * D * ((lam : ℝ) ^ (k - 16)) ^ 2

/-- With the unrounded `128² · 23.39`, K = 82 holds and K = 81 fails. -/
theorem p0101_unrounded : 0 < sq101 (2339 / 100) 82 ∧ sq101 (2339 / 100) 81 < 0 := by
  obtain ⟨h1, h2⟩ := pi_sq_bounds
  have h0 : (0 : ℝ) < π ^ 2 := by positivity
  unfold sq101 lam
  constructor
  · have : (556388 / 100000 * (3141592 / 1000000 : ℝ) ^ 2 / 16) ^ 2 ≤
        (556388 / 100000 * π ^ 2 / 16) ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num); nlinarith
    norm_num at this ⊢; linarith
  · have : (556388 / 100000 * π ^ 2 / 16) ^ 2 ≤
        (556388 / 100000 * (3141593 / 1000000 : ℝ) ^ 2 / 16) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); nlinarith
    norm_num at this ⊢; linarith

/-! ### P0102, page 91 -/

/-- P0102 closing inequality, page 91, in the limit `J₊(0) = J(1)`, `ε = 0`:
`100.09741 - D (8 · 16)² λ^{k' - 28}` with `D = 23.39` printed. The paper has
`J(1) ≤ J(0) ≤ J₊(0) ≤ (1 + O(η)) J(1)`. -/
def margin102 (D : ℚ) (k' : ℕ) : ℚ := 10009741 / 100000 - D * 128 ^ 2 * lam ^ (k' - 28)

/-- P0102: the least `k'` is 96, then `k = k' + 2 = 98` after reaching `4 mod 8`. -/
theorem p0102_reproduced : 0 < margin102 (2339 / 100) 96 ∧ margin102 (2339 / 100) 95 < 0 := by
  unfold margin102 lam; norm_num

/-- The 96 survives the `(16 + ε)` and `J₊(0)/J(1)` losses: positive with
`(8 · 16.001)²` and a factor `1.001`. -/
theorem p0102_robust :
    0 < 10009741 / 100000 - (2339 / 100) * (8 * (16001 / 1000)) ^ 2 * (1001 / 1000) * lam ^ 68 := by
  unfold lam; norm_num

/-! ### The local factor at `p = 5`, both papers' page with `κ(h)` -/

/-- Each paper's own table: `B(5, h) = (p - 1)(p² + 6p + 1) = 224` when `5 ∣ h`, so the
factor `1 + B/(p - 1)⁴` is `15/8`; at `p = 3`, `3 ∣ h`, it is `3`. -/
theorem local_factors :
    (1 : ℚ) + (5 - 1) * (5 ^ 2 + 6 * 5 + 1) / (5 - 1) ^ 4 = 15 / 8 ∧
    (1 : ℚ) + (3 - 1) * (3 + 1) ^ 2 / (3 - 1) ^ 4 = 3 := by norm_num

/-- For `5 ∤ h` the factor at 5 is `(25 - 15 (h/5))/32`; both papers, after Zhao, print
`25 + 15 (h/5)`; the sign does not matter after `(25 ± 15χ)² ≤ 25² + 15²` on average. -/
theorem local_factor_5_ndvd (χ : ℚ) :
    1 + (-(5 ^ 2 + 6 * 5 + 1) - 4 * 5 * (5 + 1) * χ) / (5 - 1) ^ 4 = (25 - 15 * χ) / 32 := by
  ring

/-- `8.54` is `9 c₄²` with `c₄ ≤ 0.9743`, rounded: `9 · 0.9743² = 8.5433...`. -/
theorem c854 : (9 : ℚ) * (9743 / 10000) ^ 2 ≤ 854 / 100 + 34 / 10000 := by norm_num

/-- The papers' coefficients `7.0889 = 8.54 · 850/1024` and
`14.0026 = 8.54 ((3/2)² - (25/32)²)`, and the corrected second coefficient with `15/8`
in place of `3/2`, `8.54 ((15/8)² - 850/1024) = 22.9345...`. -/
theorem coeff_printed :
    (854 / 100 : ℚ) * (25 ^ 2 + 15 ^ 2) / 32 ^ 2 = 7088867187500 / 1000000000000 ∧
    (854 / 100 : ℚ) * ((3 / 2) ^ 2 - (25 / 32) ^ 2) = 14002597656250 / 1000000000000 := by
  norm_num

theorem coeff_corrected :
    (854 / 100 : ℚ) * ((15 / 8) ^ 2 - (25 ^ 2 + 15 ^ 2) / 32 ^ 2) = 22934570312500 / 1000000000000 := by
  norm_num

/-- If the printed split `7.0889 c₁ + 14.0026 c₂ ≤ 23.39` holds with `0 ≤ c₂ ≤ c₁`, the
corrected bound `7.0889 c₁ + 22.9346 c₂` is at most `33.3`. The hypotheses `hsplit` and
`hmono` are the papers' unprinted numerics and the monotonicity `β(3d) ≤ β(15d)`. -/
theorem corrected_le (c₁ c₂ : ℝ) (_h₂ : 0 ≤ c₂) (hmono : c₂ ≤ c₁)
    (hsplit : 70889 / 10000 * c₁ + 140026 / 10000 * c₂ ≤ 2339 / 100) :
    70889 / 10000 * c₁ + 229346 / 10000 * c₂ ≤ 333 / 10 := by
  nlinarith

/-- Worst case for P0102: with `D ≤ 33.3`, `k' = 99` works, so `k = 101`. -/
theorem p0102_worst (D : ℚ) (hD : D ≤ 333 / 10) : 0 < margin102 D 99 := by
  have h : 0 < margin102 (333 / 10) 99 := by unfold margin102 lam; norm_num
  unfold margin102 at h ⊢
  have : 0 ≤ (128 : ℚ) ^ 2 * lam ^ (99 - 28) := by unfold lam; positivity
  nlinarith [mul_le_mul_of_nonneg_right hD this]

/-- Worst case for P0101: with `D ≤ 33.3`, `K = 84` works. -/
theorem p0101_worst (D : ℝ) (hD : D ≤ 333 / 10) : 0 < sq101 D 84 := by
  obtain ⟨h1, -⟩ := pi_sq_bounds
  have hA : (556388 / 100000 * (3141592 / 1000000 : ℝ) ^ 2 / 16) ^ 2 ≤
      (556388 / 100000 * π ^ 2 / 16) ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num); nlinarith
  have hl : 0 ≤ (((lam : ℝ)) ^ (84 - 16)) ^ 2 := by positivity
  have key : 0 < (556388 / 100000 * (3141592 / 1000000 : ℝ) ^ 2 / 16) ^ 2 -
      3058869 / 10000 * 128 ^ 2 * (333 / 10) * (((lam : ℝ)) ^ (84 - 16)) ^ 2 := by
    unfold lam; norm_num
  unfold sq101
  nlinarith

/-! ### Hathi Lemma 3.1 against Hathi's own definitions 2.7, 2.8, 2.10 -/

/-- `N_l(d)` of Hathi (2.7), with `u_j, v_j` running over `1..ρ`, written `i + 1` for
`i : Fin ρ`. -/
def Nl (l d ρ : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin l → Fin ρ × Fin ρ)).filter (fun x =>
    ((∑ j, ((2 : ℤ) ^ ((x j).1.val + 1) - 2 ^ ((x j).2.val + 1))) % (d : ℤ)) = 0)).card

/-- The order of 2 modulo 3 is 2. -/
theorem rho3 : 2 ^ 2 % 3 = 1 ∧ 2 ^ 1 % 3 ≠ 1 := by decide

theorem N1_3 : Nl 1 3 2 = 2 := by decide +kernel
theorem N5_3 : Nl 5 3 2 = 342 := by decide +kernel

/-- `c₁,ₗ` as a sum of nonnegative terms whose `d = 1` term is `1/β_l(3) = N_l(3)/ρ^{2l}`
is at least that term. `f` stands for `d ↦ μ²(d)/(c(d) β_l(3d))` on `d` with prime factors
above 5, and 0 elsewhere. -/
theorem c1_ge_first (f : ℕ → ℝ) (hf : Summable f) (h0 : ∀ d, 0 ≤ f d) :
    f 1 ≤ ∑' d, f d := hf.le_tsum 1 (fun j _ => h0 j)

/-- Hathi's `c_{0,1} = 75/32 c_{1,1} + 105/32 c_{2,1}` exceeds the printed bound `1.127`:
the `d = 1` term of `c_{1,1}` is `1/β₁(3) = N₁(3)/2² = 1/2`, and `75/64 > 1.127`. -/
theorem hathi_c01_gt (f g : ℕ → ℝ) (hf : Summable f) (_hg : Summable g)
    (hf0 : ∀ d, 0 ≤ f d) (hg0 : ∀ d, 0 ≤ g d) (hf1 : f 1 = (Nl 1 3 2 : ℝ) / 2 ^ 2) :
    (1127 / 1000 : ℝ) < 75 / 32 * (∑' d, f d) + 105 / 32 * (∑' d, g d) := by
  have a := c1_ge_first f hf hf0
  have b : 0 ≤ ∑' d, g d := tsum_nonneg hg0
  rw [hf1, N1_3] at a
  norm_num at a
  nlinarith

/-- Hathi's `c_{0,5}` exceeds the printed `0.7773`: the `d = 1` term of `c_{1,5}` is
`N₅(3)/2¹⁰ = 342/1024`, and `75/32 · 342/1024 = 0.78277 > 0.7773`. -/
theorem hathi_c05_gt (f g : ℕ → ℝ) (hf : Summable f)
    (hf0 : ∀ d, 0 ≤ f d) (hg0 : ∀ d, 0 ≤ g d) (hf1 : f 1 = (Nl 5 3 2 : ℝ) / 2 ^ 10) :
    (7773 / 10000 : ℝ) < 75 / 32 * (∑' d, f d) + 105 / 32 * (∑' d, g d) := by
  have a := c1_ge_first f hf hf0
  have b : 0 ≤ ∑' d, g d := tsum_nonneg hg0
  rw [hf1, N5_3] at a
  norm_num at a
  nlinarith

/-- Downstream in P0080 section 4: the criterion `0.9 - λ₀^{k' - 2l} · 11 · c` of
`Statements.margin` at `l = 5`, `k' = 29` fails for every `c ≥ 0.844`. The Python check
U6827_pair.out gives `c_{0,5} ≥ 75/(32 β₅(3)) + 105/(32 β₅(15)) = 1.00366` from the two
`d = 1` terms, so if 2.10 is the right definition, k' = 29 does not follow from section 4;
the least k' there is 31. This is a QUESTION on P0080, not a finding. -/
theorem hathi_k29_fails_of (c : ℚ) (hc : 844 / 1000 ≤ c) :
    9 / 10 - (8844473 / 10000000 : ℚ) ^ (29 - 2 * 5) * 11 * c < 0 := by
  have h : 9 / 10 - (8844473 / 10000000 : ℚ) ^ (29 - 2 * 5) * 11 * (844 / 1000) < 0 := by
    norm_num
  have : 0 ≤ (8844473 / 10000000 : ℚ) ^ (29 - 2 * 5) * 11 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc this]

end LeanLab.Hathi2021.PairLinnik
