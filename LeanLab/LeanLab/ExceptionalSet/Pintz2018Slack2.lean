/-
P0016 Pintz 2018, arXiv 1804.09084v2, unit U-6790, CLOUD 20261021T0017Z-cloud54, T2.
Section 9 at the weight `A'' = 25/7 - 1/350 = 1249/350`, so `ϑ'' = 350/1249 = 0.280224...` and
`1 - ϑ'' = 899/1249 = 0.719776...`, with Case 7 resting on the cut `Λ₁ = 2.421` bounds.

Background. U-6775, `Pintz2018Slack.lean`, closed Section 9 at `25/7 - 1/20000` with Case 7
binding, because it used `max b_i ≤ 0.0715` for every class. The falsifier U-6783,
`Falsifier6783.md`, found that Case 7 on p. 42 defines `a_i, b_i` with the cut `Λ₁`, where the
paper's own zero lower bounds of pp. 38 to 39 give much smaller `b_i`. Here Case 7 rests on the
named hypothesis `Case7AtLambda1`: typical classes `b_i(25/7, Λ₁) ≤ 0.0085` and the `χ₁` class
`b_{i₁}(25/7, Λ₁) ≤ 0.0625`. These are a LAB RECONSTRUCTION, numerics/falsifier_U6783.py, not
printed values. The `χ₁` half is derived in Lean, `case7AtLambda1_of_lemma6`, from (9.5) Case 4
read as `0.0715`, the printed `0.715` taken as a misprint, by monotonicity in the cut; the typical
half, `0.0085`, is the falsifier's loose variant, 45 zeros at `Λ₁` plus the allowance above 3
implied by `c₁* = 0.0722`, and stays a hypothesis.

Numerics, numerics/slack2_U6790.py and .out, mpmath: with the transfer of U-6775 and the best
single `c`, Cases 1 to 6 bind, and close for `η < 0.0029948`; Case 7 at the `Λ₁` bounds closes
for `η < 0.0877`; Case 8 for every `A ≥ 7/2`. The certified choice `η = 1/350` gives Cases 1 to 6
`S₀ < 0.9997`, numerically `0.99922`, Case 7 `S₀ < 0.9`, Case 8 `S₀ < 1`.

HONESTY. The exponent `0.719776` is below `0.72`, but this is at most a CONDITIONAL observation
that Pintz's own printed margin in Section 9 allows a slightly smaller exponent. It rests on
(i) the unformalized step from `S₀ ≤ 1 - c₀` to `NonSiegelInput`, Theorems A to L and the
reduction of Section 2, none proved here; (ii) Lemma 6 and Lemma 7 values at `A = 25/7`, quoted;
(iii) the reconstructed `Λ₁` bound `0.0085`. It is NOT a new record: Zhao 2025,
arXiv 2511.05631, claims `E(X) = O(X^{7/10})`, v1 `X^{0.709}`, a preprint, both below `0.7198`.
Prior-art search 2026-10-21, WebSearch: nearest results Zhao 2025 `7/10`, Pintz 2018 `0.72`,
Bhowmik and Grimmelt 2026 arXiv 2607.27282, a survey with a new explicit major arc formula that
quotes `δ = 0.28` and claims no smaller exponent. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ExceptionalSet.Pintz2018Slack

namespace LeanLab.ExceptionalSet.Pintz2018Slack2
open Real Finset
open LeanLab.ExceptionalSet.Pintz2018Slack

attribute [local instance] Classical.propDecidable

/-! ### Parameters -/

/-- The reduced weight `A'' = 25/7 - η`, `η = 1/350`. -/
noncomputable def A2 : ℝ := 25 / 7 - 1 / 350

theorem A2_eq : A2 = 1249 / 350 := by unfold A2; norm_num

/-- `ϑ'' = 1/A'' = 350/1249`, `1 - ϑ'' = 899/1249 < 0.71978 < 0.72`. -/
theorem exponent2 : 1 / A2 = 350 / 1249 ∧ 1 - 1 / A2 = 899 / 1249 ∧
    (899 / 1249 : ℝ) < 0.71978 ∧ (0.71978 : ℝ) < 0.72 := by
  rw [A2_eq]; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `A'' = t·(25/7) + (1-t)·(8/3)` with `t = 947/950`, and `tc + (1-t)d = 0` for
`c = 3/160`, `d = -947/160`. -/
theorem transfer_params2 :
    A2 = 947 / 950 * (25 / 7) + (1 - 947 / 950) * (8 / 3) ∧
    (947 / 950 : ℝ) * (3 / 160) + (1 - 947 / 950) * (-947 / 160) = 0 := by
  rw [A2_eq]; constructor <;> norm_num

/-! ### Numerical facts -/

theorem s2_exp_c : exp (3 / 160 : ℝ) ≤ 1.01893 := by
  have h := Real.exp_bound (x := (3 / 160 : ℝ)) (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (n := 3) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  linarith

theorem s2_exp_d : exp (-947 / 160 : ℝ) ≤ 0.00269 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 5.91875 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-947 / 160 : ℝ) ≤ exp (-5.91875) := exp_le_exp.mpr (by norm_num)
  linarith

/-- `α = (A''/A) t e^c ≤ 1.0149`. -/
theorem alpha2_le : A2 / (25 / 7) * (947 / 950) * exp (3 / 160) ≤ 1.0149 := by
  have := s2_exp_c
  rw [A2_eq]
  nlinarith

/-- `β = (A''/B)(1-t) e^d ≤ 1.14 · 10⁻⁵`. -/
theorem beta2_le : A2 / (8 / 3) * (1 - 947 / 950) * exp (-947 / 160) ≤ 0.0000114 := by
  have := s2_exp_d
  rw [A2_eq]
  nlinarith

theorem alpha2_pos : 0 < A2 / (25 / 7) * (947 / 950) * exp (3 / 160) := by
  rw [A2_eq]; positivity

theorem beta2_pos : 0 < A2 / (8 / 3) * (1 - 947 / 950) * exp (-947 / 160) := by
  rw [A2_eq]; norm_num; positivity

theorem s2_e1 : exp ((1 / 350 : ℝ) * 1.311) ≤ 1.003754 := by
  have h := Real.exp_bound (x := (1 / 350 : ℝ) * 1.311)
    (by rw [abs_of_nonneg (by norm_num)]; norm_num) (n := 3) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  norm_num
  linarith

theorem s2_e2 : exp (-((A2 - 8 / 3) * 1.311)) ≤ 0.30658 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 1.1823 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-((A2 - 8 / 3) * 1.311)) ≤ exp (-1.1823) :=
    exp_le_exp.mpr (by rw [A2_eq]; norm_num)
  linarith

theorem s2_c7a : exp (-(A2 * 0.04)) ≤ 0.86698 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 0.14274 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-(A2 * 0.04)) ≤ exp (-0.14274) := exp_le_exp.mpr (by rw [A2_eq]; norm_num)
  linarith

theorem s2_c7b : exp (-((A2 - 8 / 3) * 2.421)) ≤ 0.11265 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 2.1835 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-((A2 - 8 / 3) * 2.421)) ≤ exp (-2.1835) :=
    exp_le_exp.mpr (by rw [A2_eq]; norm_num)
  linarith

theorem chi1_lo : (0.009258 : ℝ) ≤ exp (-(25 / 7 * 1.311)) := by
  have h1 := LeanLab.Pintz2018.expneg_lower 4.6822 (by norm_num) (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-4.6822) ≤ exp (-(25 / 7 * 1.311)) := exp_le_exp.mpr (by norm_num)
  linarith

theorem chi1_hi : exp (-(25 / 7 * 2.421)) ≤ (0.000176 : ℝ) := by
  have h1 := LeanLab.Pintz2018.expneg_upper 8.6464 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-(25 / 7 * 2.421)) ≤ exp (-8.6464) := exp_le_exp.mpr (by norm_num)
  linarith

/-! ### Case 7 at the cut `Λ₁` -/

section Cases
variable {ι κ : Type*}

/-- Monotonicity of `b_i` in the cut, with the drop of one zero below the lower cut:
for `Λ₀ ≤ Λ₁` and a zero `j₁` with `λ_{j₁} ≤ Λ₀`,
`b(A, Λ₁) + (e^{-AΛ₀} - e^{-AΛ₁}) ≤ b(A, Λ₀)`. PROVED, no input. -/
theorem bS_drop {A Λ0 Λ1 H : ℝ} (hA : 0 ≤ A) (h01 : Λ0 ≤ Λ1) {s : Finset ι} {lam : ι → ℝ}
    {j1 : ι} (hj1 : j1 ∈ s) (hl : lam j1 ≤ Λ0) :
    bS A Λ1 H s lam + (exp (-(A * Λ0)) - exp (-(A * Λ1))) ≤ bS A Λ0 H s lam := by
  unfold bS
  rw [← add_sum_erase s _ hj1, ← add_sum_erase s _ hj1]
  have e0 : max (lam j1) Λ0 = Λ0 := max_eq_right hl
  have e1 : max (lam j1) Λ1 = Λ1 := max_eq_right (hl.trans h01)
  rw [e0, e1]
  have hrest : ∑ x ∈ s.erase j1, (exp (-(A * max (lam x) Λ1)) - exp (-(A * H))) ≤
      ∑ x ∈ s.erase j1, (exp (-(A * max (lam x) Λ0)) - exp (-(A * H))) := by
    apply sum_le_sum
    intro j _
    have : exp (-(A * max (lam j) Λ1)) ≤ exp (-(A * max (lam j) Λ0)) :=
      exp_le_exp.mpr (by nlinarith [max_le_max (le_refl (lam j)) h01])
    linarith
  linarith

/-- **The named Case 7 input at `Λ₁ = 2.421`, a LAB RECONSTRUCTION, not printed values.**
Every class other than the class `i₁` of `χ₁` has `b_i(25/7, Λ₁) ≤ 0.0085`, and the `χ₁` class
has `b_{i₁}(25/7, Λ₁) ≤ 0.0625`. Source: falsifier U-6783, numerics/falsifier_U6783.py, from the
zero lower bounds on pp. 38 to 39 of P0016.

Plain math: `b_i = Σ_{j ∈ Z_i} (e^{-(25/7) max(λ_j, 2.421)} - e^{-(25/7) H})` is at most `0.0085`
for `i ≠ i₁` and at most `0.0625` for `i = i₁`. -/
def Case7AtLambda1 (I : Finset κ) (Z : κ → Finset ι) (lam : ι → ℝ) (H : ℝ) (i1 : κ) : Prop :=
  (∀ i ∈ I, i ≠ i1 → bS (25 / 7) 2.421 H (Z i) lam ≤ 0.0085) ∧
    bS (25 / 7) 2.421 H (Z i1) lam ≤ 0.0625

/-- The `χ₁` half of `Case7AtLambda1` from Lemma 6 Case 4. CONDITIONAL ON `h95`, (9.5) and (9.28)
read as `c₄* = 0.0715` at the cut `Λ₀ = 1.311`, the printed `0.715` taken as a misprint, and on
`htyp`, the reconstructed typical bound.

Plain math: if the class `i₁` contains a zero `λ_{j₁} ≤ 1.311` and `b_{i₁}(25/7, 1.311) ≤ 0.0715`,
then `b_{i₁}(25/7, 2.421) ≤ 0.0715 - (e^{-(25/7)1.311} - e^{-(25/7)2.421}) ≤ 0.0625`. -/
theorem case7AtLambda1_of_lemma6 {I : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {H : ℝ}
    {i1 : κ} {j1 : ι} (hj1 : j1 ∈ Z i1) (hl : lam j1 ≤ 1.311)
    (htyp : ∀ i ∈ I, i ≠ i1 → bS (25 / 7) 2.421 H (Z i) lam ≤ 0.0085)
    (h95 : bS (25 / 7) 1.311 H (Z i1) lam ≤ 0.0715) : Case7AtLambda1 I Z lam H i1 := by
  refine ⟨htyp, ?_⟩
  have hd := bS_drop (A := 25 / 7) (Λ0 := 1.311) (Λ1 := 2.421) (H := H) (by norm_num)
    (by norm_num) hj1 hl
  have := chi1_lo
  have := chi1_hi
  have e0 : exp (-(25 / 7 * (1.311 : ℝ))) = exp (-((25 / 7) * 1.311)) := rfl
  linarith

/-- Vacuity for `case7AtLambda1_of_lemma6`: one class, one zero at `0.1`, `H = 2.421`. -/
theorem case7AtLambda1_of_lemma6_vacuity :
    Case7AtLambda1 ({0} : Finset ℕ) (fun _ => ({0} : Finset ℕ)) (fun _ => (0.1 : ℝ)) 2.421 0 := by
  refine case7AtLambda1_of_lemma6 (j1 := 0) (by simp) (by norm_num)
    (by intro i hi h; simp at hi; exact absurd hi h) ?_
  simp only [bS, sum_singleton]
  rw [max_eq_right (by norm_num : (0.1 : ℝ) ≤ 1.311)]
  have h1 := LeanLab.Pintz2018.expneg_upper 4.6821 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-(25 / 7 * (1.311 : ℝ))) ≤ exp (-4.6821) := exp_le_exp.mpr (by norm_num)
  have := exp_pos (-(25 / 7 * (2.421 : ℝ)))
  linarith

/-- Case 7 numbers at `A''`. -/
theorem case7_numbers2 {a b1 m Sb : ℝ} (ha0 : 0 ≤ a) (hb10 : 0 ≤ b1)
    (ha : a ≤ 0.86698) (hSb0 : 0 ≤ Sb) (hSb : Sb ≤ 15.6 * 0.11265)
    (hb1 : b1 ≤ 1.0149 * 0.0625 + 0.0000114 * 15.6) (_hm0 : 0 ≤ m)
    (hm : m ≤ 1.0149 * 0.0085 + 0.0000114 * 15.6) :
    (a + b1) ^ 2 + m * Sb < 0.9 := by
  have h1 : (a + b1) ^ 2 ≤ (0.86698 + (1.0149 * 0.0625 + 0.0000114 * 15.6)) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith); linarith
  have h2 : m * Sb ≤ (1.0149 * 0.0085 + 0.0000114 * 15.6) * (15.6 * 0.11265) :=
    mul_le_mul hm hSb hSb0 (by norm_num)
  have : (0.86698 + (1.0149 * 0.0625 + 0.0000114 * 15.6)) ^ 2 +
      (1.0149 * 0.0085 + 0.0000114 * 15.6) * (15.6 * 0.11265) < (0.9 : ℝ) := by norm_num
  linarith

/-- **Case 7 at `A'' = 25/7 - 1/350`.** CONDITIONAL ON `hC7 : Case7AtLambda1`, the LAB
RECONSTRUCTION at `Λ₁`; on `h927`, the Corollary 1 total behind (9.27); and on `hsingle`, `hl1`,
Tables 4 and 5 of [9]: one zero `ϱ₁` with `λ₁ ≥ 0.04`, all others at `λ ≥ Λ₁ = 2.421`.

Plain math: let classes `i ∈ I` have zeros `λ_j ≤ H`, `H ≥ 2.421`. If the only zero below `2.421`
is `λ₁ ≥ 0.04`, in class `i₁`, every other class has `b_i(25/7, 2.421) ≤ 0.0085`, the class `i₁`
has `b_{i₁}(25/7, 2.421) ≤ 0.0625`, and `Σ_j e^{-(8/3)max(λ_j, 2.421)} ≤ 15.6`, then at weight
`A''` and cut `2.421`, `S₀ = Σ_i (a_i + b_i)² < 0.9`. -/
theorem case7_closes2 {I : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {H : ℝ} {i1 : κ}
    {j1 : ι} (hH : 2.421 ≤ H) (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H) (hi1 : i1 ∈ I)
    (hj1 : j1 ∈ Z i1) (hsingle : ∀ i ∈ I, ∀ j ∈ Z i, lam j < 2.421 → i = i1 ∧ j = j1)
    (hl1 : 0.04 ≤ lam j1) (hC7 : Case7AtLambda1 I Z lam H i1)
    (h927 : ∑ i ∈ I, KS (8 / 3) 2.421 (Z i) lam ≤ 15.6) :
    ∑ i ∈ I, (aS A2 2.421 (Z i) lam + bS A2 2.421 H (Z i) lam) ^ 2 < 0.9 := by
  obtain ⟨hA2, hcd⟩ := transfer_params2
  have hA20 : 0 ≤ A2 := by rw [A2_eq]; norm_num
  have hα := alpha2_pos
  have hβ := beta2_pos
  have hαu := alpha2_le
  have hβu := beta2_le
  set α := A2 / (25 / 7) * (947 / 950) * exp (3 / 160) with hαd
  set β := A2 / (8 / 3) * (1 - 947 / 950) * exp (-947 / 160) with hβd
  obtain ⟨htyp, hchi⟩ := hC7
  -- transfer of each `b_i`
  have htr : ∀ i ∈ I, ∀ c : ℝ, bS (25 / 7) 2.421 H (Z i) lam ≤ c →
      bS A2 2.421 H (Z i) lam ≤ α * c + β * 15.6 := by
    intro i hi c hc
    have ht := bS_transfer (A := 25 / 7) (B := 8 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hA2 hcd (hZH i hi) hH
    rw [← hαd, ← hβd] at ht
    have hK : bS (8 / 3) 2.421 H (Z i) lam ≤ 15.6 :=
      (bS_le_KS _ _ _ _ _).trans ((single_le_sum (fun i _ => KS_nonneg _ _ (Z i) lam) hi).trans h927)
    have := mul_le_mul_of_nonneg_left hc hα.le
    have := mul_le_mul_of_nonneg_left hK hβ.le
    linarith
  have hb1 : bS A2 2.421 H (Z i1) lam ≤ 1.0149 * 0.0625 + 0.0000114 * 15.6 := by
    have := htr i1 hi1 _ hchi
    nlinarith
  have hm : ∀ i ∈ I.erase i1, bS A2 2.421 H (Z i) lam ≤ 1.0149 * 0.0085 + 0.0000114 * 15.6 := by
    intro i hi
    obtain ⟨hne, hiI⟩ := mem_erase.mp hi
    have := htr i hiI _ (htyp i hiI hne)
    nlinarith
  -- `a_i = 0` off the class `i₁`
  have ha0 : ∀ i ∈ I.erase i1, aS A2 2.421 (Z i) lam = 0 := by
    intro i hi
    obtain ⟨hne, hiI⟩ := mem_erase.mp hi
    unfold aS
    apply sum_eq_zero
    intro j hj
    have : 2.421 ≤ lam j := by
      by_contra h; push Not at h; exact hne (hsingle i hiI j hj h).1
    rw [min_eq_right this]; ring
  -- `a_{i₁} ≤ e^{-A''·0.04}`
  have ha1 : aS A2 2.421 (Z i1) lam ≤ 0.86698 := by
    have hs := aS_single (A := A2) hi1 hj1 hsingle
    have hle : aS A2 2.421 (Z i1) lam ≤ ∑ i ∈ I, aS A2 2.421 (Z i) lam :=
      single_le_sum (fun i _ => aS_nonneg hA20 (Z i) lam) hi1
    have : exp (-(A2 * min (lam j1) 2.421)) ≤ exp (-(A2 * 0.04)) :=
      exp_le_exp.mpr (by nlinarith [le_min hl1 (by norm_num : (0.04 : ℝ) ≤ 2.421)])
    have := s2_c7a
    have := exp_pos (-(A2 * 2.421))
    linarith
  -- the `b`-sum
  have hbsum : ∑ i ∈ I, bS A2 2.421 H (Z i) lam ≤ 15.6 * 0.11265 := by
    have he := s2_c7b
    calc ∑ i ∈ I, bS A2 2.421 H (Z i) lam
        ≤ ∑ i ∈ I, exp (-((A2 - 8 / 3) * 2.421)) * KS (8 / 3) 2.421 (Z i) lam :=
          sum_le_sum fun i _ => bS_tail (by rw [A2_eq]; norm_num) _ _
      _ = exp (-((A2 - 8 / 3) * 2.421)) * ∑ i ∈ I, KS (8 / 3) 2.421 (Z i) lam := by rw [mul_sum]
      _ ≤ 0.11265 * 15.6 := mul_le_mul he h927
          (sum_nonneg fun i _ => KS_nonneg _ _ _ _) (by norm_num)
      _ = 15.6 * 0.11265 := by ring
  have hbnn : ∀ i ∈ I, 0 ≤ bS A2 2.421 H (Z i) lam := fun i hi => bS_nonneg hA20 (hZH i hi) hH
  have hsub : ∑ i ∈ I.erase i1, bS A2 2.421 H (Z i) lam ≤ ∑ i ∈ I, bS A2 2.421 H (Z i) lam :=
    sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i hi _ => hbnn i hi)
  have hrest : ∑ i ∈ I.erase i1, (aS A2 2.421 (Z i) lam + bS A2 2.421 H (Z i) lam) ^ 2 ≤
      (1.0149 * 0.0085 + 0.0000114 * 15.6) * ∑ i ∈ I.erase i1, bS A2 2.421 H (Z i) lam := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    rw [ha0 i hi, zero_add, sq]
    have hb0 := hbnn i (mem_of_mem_erase hi)
    have := hm i hi
    nlinarith
  rw [← add_sum_erase I _ hi1]
  have hn := case7_numbers2 (aS_nonneg hA20 (Z i1) lam) (hbnn i1 hi1) ha1
    (sum_nonneg fun i hi => hbnn i (mem_of_mem_erase hi)) (hsub.trans hbsum) hb1 (by norm_num)
    le_rfl
  linarith

/-- Vacuity instance for `case7_closes2`: one class, one zero at `λ₁ = 0.1`, `H = Λ₁`; every
hypothesis holds, `Case7AtLambda1` by `case7AtLambda1_of_lemma6_vacuity`. -/
theorem case7_closes2_vacuity :
    ∑ _i ∈ ({0} : Finset ℕ), (aS A2 2.421 ({0} : Finset ℕ) (fun _ => (0.1 : ℝ)) +
      bS A2 2.421 2.421 ({0} : Finset ℕ) (fun _ => (0.1 : ℝ))) ^ 2 < 0.9 := by
  have := case7_closes2 (ι := ℕ) (κ := ℕ) (I := {0}) (Z := fun _ => {0})
    (lam := fun _ => (0.1 : ℝ)) (H := 2.421) (i1 := 0) (j1 := 0) le_rfl
    (by intro _ _ _ _; norm_num) (by simp) (by simp)
    (by intro i hi j hj _; simp_all) (by norm_num) case7AtLambda1_of_lemma6_vacuity
    (by
      simp only [KS, sum_singleton]
      have : exp (-(8 / 3 * max (0.1 : ℝ) 2.421)) ≤ 1 := exp_le_one_iff.mpr (by
        rw [max_eq_right (by norm_num : (0.1 : ℝ) ≤ 2.421)]; norm_num)
      linarith)
  simpa using this

/-! ### Cases 1 to 6 at `A''` -/

/-- **Cases 1 to 6 at `A'' = 25/7 - 1/350`.** CONDITIONAL ON the same quoted inputs at
`A = 25/7` as `Pintz2018Slack.cases1to6_closes`: `h920`, (9.20), `Σ_i a_i ≤ 0.622`; Lemma 6,
(9.5), as used in (9.22) to (9.26), `b_i ≤ 0.0722` outside `I₂ ∪ I₃`, `≤ 0.0751` on `I₂`,
`≤ 0.0826` everywhere, `|I₂|, |I₃| ≤ 2`; `h96`, the Corollary 1 total of (9.6), `≤ 22.281`.
These are the binding cases: numerically they close only for `η < 0.0029948`.

Plain math: under these, at weight `A''` and cut `Λ₀ = 1.311`, `S₀ = Σ_i (a_i + b_i)² < 0.9997`.
The value is `0.99922`; the paper's (9.21) proof gives `S < 0.9832` at `25/7`. -/
theorem cases1to6_closes2 {I I2 I3 : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {H : ℝ}
    (hH : 1.311 ≤ H) (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H)
    (h920 : ∑ i ∈ I, aS (25 / 7) 1.311 (Z i) lam ≤ 0.622)
    (h1 : ∀ i ∈ I, i ∉ I2 → i ∉ I3 → bS (25 / 7) 1.311 H (Z i) lam ≤ 0.0722)
    (h2 : ∀ i ∈ I, i ∈ I2 → bS (25 / 7) 1.311 H (Z i) lam ≤ 0.0751)
    (h3 : ∀ i ∈ I, bS (25 / 7) 1.311 H (Z i) lam ≤ 0.0826)
    (hI2 : I2.card ≤ 2) (hI3 : I3.card ≤ 2)
    (h96 : ∑ i ∈ I, KS (8 / 3) 1.311 (Z i) lam ≤ 22.281) :
    ∑ i ∈ I, (aS A2 1.311 (Z i) lam + bS A2 1.311 H (Z i) lam) ^ 2 < 0.9997 := by
  obtain ⟨hA2, hcd⟩ := transfer_params2
  have hA20 : 0 ≤ A2 := by rw [A2_eq]; norm_num
  have hα := alpha2_pos
  have hβ := beta2_pos
  have hαu := alpha2_le
  have hβu := beta2_le
  set α := A2 / (25 / 7) * (947 / 950) * exp (3 / 160) with hαd
  set β := A2 / (8 / 3) * (1 - 947 / 950) * exp (-947 / 160) with hβd
  have hK : ∀ i ∈ I, bS (8 / 3) 1.311 H (Z i) lam ≤ 22.281 := fun i hi =>
    (bS_le_KS _ _ _ _ _).trans ((single_le_sum (fun i _ => KS_nonneg _ _ (Z i) lam) hi).trans h96)
  have htr : ∀ i ∈ I, ∀ c : ℝ, bS (25 / 7) 1.311 H (Z i) lam ≤ c →
      bS A2 1.311 H (Z i) lam ≤ α * c + β * 22.281 := by
    intro i hi c hc
    have ht := bS_transfer (A := 25 / 7) (B := 8 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hA2 hcd (hZH i hi) hH
    rw [← hαd, ← hβd] at ht
    have := mul_le_mul_of_nonneg_left hc hα.le
    have := mul_le_mul_of_nonneg_left (hK i hi) hβ.le
    linarith
  have hasum : ∑ i ∈ I, aS A2 1.311 (Z i) lam ≤ exp ((1 / 350) * 1.311) * 0.622 := by
    have hs : ∀ i ∈ I, aS A2 1.311 (Z i) lam ≤ exp ((1 / 350) * 1.311) *
        aS (25 / 7) 1.311 (Z i) lam := fun i _ => by
      have := aS_scale (A := 25 / 7) (η := 1 / 350) (Λ := 1.311) (by norm_num) (Z i) lam
      simpa [A2] using this
    calc ∑ i ∈ I, aS A2 1.311 (Z i) lam
        ≤ ∑ i ∈ I, exp ((1 / 350) * 1.311) * aS (25 / 7) 1.311 (Z i) lam := sum_le_sum hs
      _ = exp ((1 / 350) * 1.311) * ∑ i ∈ I, aS (25 / 7) 1.311 (Z i) lam := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h920 (exp_pos _).le
  have hbsum : ∑ i ∈ I, bS A2 1.311 H (Z i) lam ≤ 22.281 * exp (-((A2 - 8 / 3) * 1.311)) := by
    calc ∑ i ∈ I, bS A2 1.311 H (Z i) lam
        ≤ ∑ i ∈ I, exp (-((A2 - 8 / 3) * 1.311)) * KS (8 / 3) 1.311 (Z i) lam :=
          sum_le_sum fun i _ => bS_tail (by rw [A2_eq]; norm_num) _ _
      _ = exp (-((A2 - 8 / 3) * 1.311)) * ∑ i ∈ I, KS (8 / 3) 1.311 (Z i) lam := by rw [mul_sum]
      _ ≤ exp (-((A2 - 8 / 3) * 1.311)) * 22.281 := mul_le_mul_of_nonneg_left h96 (exp_pos _).le
      _ = _ := by ring
  have hr := refined_ineq I I2 I3 (fun i => aS A2 1.311 (Z i) lam)
    (fun i => bS A2 1.311 H (Z i) lam) (Aa := exp ((1 / 350) * 1.311) * 0.622)
    (Bb := 22.281 * exp (-((A2 - 8 / 3) * 1.311)))
    (c1 := α * 0.0722 + β * 22.281) (c2 := α * 0.0751 + β * 22.281)
    (c3 := α * 0.0826 + β * 22.281)
    (fun i _ => aS_nonneg hA20 _ _) (fun i hi => bS_nonneg hA20 (hZH i hi) hH)
    (by positivity) (by nlinarith) (by nlinarith)
    (fun i hi h2' h3' => htr i hi _ (h1 i hi h2' h3'))
    (fun i hi h2' => htr i hi _ (h2 i hi h2')) (fun i hi => htr i hi _ (h3 i hi)) hI2 hI3
    hasum hbsum
  refine lt_of_le_of_lt hr ?_
  have e1 := s2_e1
  have e2 := s2_e2
  set x := exp ((1 / 350 : ℝ) * 1.311)
  set y := exp (-((A2 - 8 / 3) * 1.311))
  have hx0 : 0 ≤ x := (exp_pos _).le
  have hy0 : 0 ≤ y := (exp_pos _).le
  have key : (x * 0.622) ^ 2 + (α * 0.0722 + β * 22.281) * (2 * (x * 0.622) + 22.281 * y) +
      (α * 0.0826 + β * 22.281 - (α * 0.0722 + β * 22.281)) *
        (2 * (x * 0.622) + 2 * (α * 0.0826 + β * 22.281)) +
      (α * 0.0751 + β * 22.281 - (α * 0.0722 + β * 22.281)) * (2 * (α * 0.0751 + β * 22.281)) =
      0.622 ^ 2 * x ^ 2 + (α * 0.0722 + β * 22.281) * (2 * 0.622 * x + 22.281 * y) +
      0.0104 * α * (2 * 0.622 * x + 2 * (α * 0.0826 + β * 22.281)) +
      0.0029 * α * (2 * (α * 0.0751 + β * 22.281)) := by ring
  rw [key]
  calc 0.622 ^ 2 * x ^ 2 + (α * 0.0722 + β * 22.281) * (2 * 0.622 * x + 22.281 * y) +
      0.0104 * α * (2 * 0.622 * x + 2 * (α * 0.0826 + β * 22.281)) +
      0.0029 * α * (2 * (α * 0.0751 + β * 22.281))
      ≤ 0.622 ^ 2 * 1.003754 ^ 2 + (1.0149 * 0.0722 + 0.0000114 * 22.281) *
          (2 * 0.622 * 1.003754 + 22.281 * 0.30658) +
        0.0104 * 1.0149 * (2 * 0.622 * 1.003754 + 2 * (1.0149 * 0.0826 + 0.0000114 * 22.281)) +
        0.0029 * 1.0149 * (2 * (1.0149 * 0.0751 + 0.0000114 * 22.281)) := by
        gcongr
    _ < 0.9997 := by norm_num

/-- Vacuity instance for `cases1to6_closes2`: one class, one zero at `λ = 2 = H`, so every
`a_i` and `b_i` vanishes and every hypothesis holds. -/
theorem cases1to6_closes2_vacuity :
    ∑ _i ∈ ({0} : Finset ℕ), (aS A2 1.311 ({0} : Finset ℕ) (fun _ => (2 : ℝ)) +
      bS A2 1.311 2 ({0} : Finset ℕ) (fun _ => (2 : ℝ))) ^ 2 < 0.9997 := by
  have hb0 : bS (25 / 7) 1.311 2 ({0} : Finset ℕ) (fun _ => (2 : ℝ)) = 0 := by
    simp only [bS, sum_singleton]; rw [max_eq_left (by norm_num : (1.311 : ℝ) ≤ 2)]; ring
  have ha0 : aS (25 / 7) 1.311 ({0} : Finset ℕ) (fun _ => (2 : ℝ)) = 0 := by
    simp only [aS, sum_singleton]; rw [min_eq_right (by norm_num : (1.311 : ℝ) ≤ 2)]; ring
  have := cases1to6_closes2 (ι := ℕ) (κ := ℕ) (I := {0}) (I2 := ∅) (I3 := ∅)
    (Z := fun _ => {0}) (lam := fun _ => (2 : ℝ)) (H := 2) (by norm_num)
    (by intro _ _ _ _; norm_num)
    (by simp only [sum_singleton]; rw [ha0]; norm_num)
    (by intro i hi _ _; simp at hi; subst hi; rw [hb0]; norm_num)
    (by intro i hi h; simp at h)
    (by intro i hi; simp at hi; subst hi; rw [hb0]; norm_num)
    (by simp) (by simp)
    (by
      simp only [KS, sum_singleton]
      have : exp (-(8 / 3 * max (2 : ℝ) 1.311)) ≤ 1 := exp_le_one_iff.mpr (by
        rw [max_eq_left (by norm_num : (1.311 : ℝ) ≤ 2)]; norm_num)
      linarith)
  simpa using this

/-! ### Case 8 for every weight `A ≥ 7/2` -/

/-- `e^{-(A-2)Λ*} ≤ λ₁^{11/7}` for `A ≥ 7/2`, when `Λ* ≥ (12/11 - ε) log(1/λ₁)`,
`0 < λ₁ ≤ 1`, `ε ≤ 1/100`. PROVED, no input. -/
theorem case8_pow_gen {A l Ls ε : ℝ} (hA : 7 / 2 ≤ A) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (hε : ε ≤ 1 / 100) (hLs : (12 / 11 - ε) * log (1 / l) ≤ Ls) :
    exp (-((A - 2) * Ls)) ≤ l ^ (11 / 7 : ℝ) := by
  have hlog : 0 ≤ log (1 / l) := log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
  have hA2 : (11 / 7 : ℝ) ≤ (A - 2) * (12 / 11 - ε) := by nlinarith
  have hA20 : 0 ≤ A - 2 := by linarith
  have h1 : 11 / 7 * log (1 / l) ≤ (A - 2) * Ls := by
    calc 11 / 7 * log (1 / l) ≤ (A - 2) * (12 / 11 - ε) * log (1 / l) :=
          mul_le_mul_of_nonneg_right hA2 hlog
      _ = (A - 2) * ((12 / 11 - ε) * log (1 / l)) := by ring
      _ ≤ (A - 2) * Ls := mul_le_mul_of_nonneg_left hLs hA20
  rw [rpow_def_of_pos hl0]
  apply exp_le_exp.mpr
  rw [one_div, log_inv] at h1
  linarith

theorem exp_neg_33_le : exp (-3.3 : ℝ) ≤ 0.0369 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 3.3 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

/-- **Case 8 at every weight `A ≥ 7/2`.** CONDITIONAL ON the same quoted inputs as
`Pintz2018Slack.case8_closes`: Theorem G and Table 5 of [9] as (9.31), one zero
`λ₁ ∈ (0, 0.04]` and all others at `λ ≥ Λ*`, `Λ* ≥ 3.96`, `Λ* ≥ (12/11 - ε) log(1/λ₁)`;
Corollary 1 as (9.32) with the term of `ϱ₁` added.

Plain math: then for every `A ≥ 7/2`, at weight `A` and cut `Λ*`, `S₀ = Σ_i (a_i + b_i)² < 1`. -/
theorem case8_closes_gen {A : ℝ} (hA : 7 / 2 ≤ A) {I : Finset κ} {Z : κ → Finset ι}
    {lam : ι → ℝ} {H Ls ε : ℝ} {i1 : κ} {j1 : ι} (hLH : Ls ≤ H)
    (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H) (hi1 : i1 ∈ I) (hj1 : j1 ∈ Z i1)
    (hsingle : ∀ i ∈ I, ∀ j ∈ Z i, lam j < Ls → i = i1 ∧ j = j1)
    (hl0 : 0 < lam j1) (hl1 : lam j1 ≤ 0.04) (hε : ε ≤ 1 / 100)
    (hLs1 : 3.96 ≤ Ls) (hLs2 : (12 / 11 - ε) * log (1 / lam j1) ≤ Ls)
    (h932a : ∑ i ∈ I, KS (8 / 3) Ls (Z i) lam ≤ 10.4 + exp (-(8 / 3 * Ls)))
    (h932b : ∀ i ∈ I, KS 2 Ls (Z i) lam ≤ 10.4 + exp (-(2 * Ls))) :
    ∑ i ∈ I, (aS A Ls (Z i) lam + bS A Ls H (Z i) lam) ^ 2 < 1 := by
  set l := lam j1
  have hA0 : 0 ≤ A := by linarith
  have hasum : ∑ i ∈ I, aS A Ls (Z i) lam ≤ exp (-(A * l)) := by
    rw [aS_single hi1 hj1 hsingle, min_eq_left (by linarith : l ≤ Ls)]
    linarith [exp_pos (-(A * Ls))]
  have hpow := case8_pow_gen hA hl0 (by linarith) hε hLs2
  have hm2 : exp (-(2 * Ls)) ≤ 0.01 := by
    have h1 := LeanLab.Pintz2018.expneg_upper 7.92 (by norm_num)
    simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
    norm_num at h1
    have : exp (-(2 * Ls)) ≤ exp (-7.92) := exp_le_exp.mpr (by linarith)
    linarith
  have hbi : ∀ i ∈ I, bS A Ls H (Z i) lam ≤ 10.41 * l ^ (11 / 7 : ℝ) := by
    intro i hi
    have h1 := bS_tail (A := A) (B := 2) (Λ := Ls) (H := H) (by linarith) (Z i) lam
    have h2 := h932b i hi
    have hp0 : 0 ≤ l ^ (11 / 7 : ℝ) := rpow_nonneg hl0.le _
    calc bS A Ls H (Z i) lam ≤ exp (-((A - 2) * Ls)) * KS 2 Ls (Z i) lam := h1
      _ ≤ l ^ (11 / 7 : ℝ) * 10.41 :=
          mul_le_mul hpow (by linarith) (KS_nonneg _ _ _ _) hp0
      _ = _ := by ring
  have hm83 : exp (-(8 / 3 * Ls)) ≤ 0.01 := by
    have : exp (-(8 / 3 * Ls)) ≤ exp (-(2 * Ls)) := exp_le_exp.mpr (by linarith)
    linarith
  have hbsum : ∑ i ∈ I, bS A Ls H (Z i) lam ≤ 0.3842 := by
    have he : exp (-((A - 8 / 3) * Ls)) ≤ 0.0369 := by
      have : exp (-((A - 8 / 3) * Ls)) ≤ exp (-3.3) := exp_le_exp.mpr (by nlinarith)
      linarith [exp_neg_33_le]
    calc ∑ i ∈ I, bS A Ls H (Z i) lam
        ≤ ∑ i ∈ I, exp (-((A - 8 / 3) * Ls)) * KS (8 / 3) Ls (Z i) lam :=
          sum_le_sum fun i _ => bS_tail (by linarith) _ _
      _ = exp (-((A - 8 / 3) * Ls)) * ∑ i ∈ I, KS (8 / 3) Ls (Z i) lam := by rw [mul_sum]
      _ ≤ 0.0369 * 10.41 := mul_le_mul he (by linarith)
          (sum_nonneg fun i _ => KS_nonneg _ _ _ _) (by norm_num)
      _ ≤ 0.3842 := by norm_num
  have hb := LeanLab.Pintz2018.basic_ineq I (fun i => aS A Ls (Z i) lam)
    (fun i => bS A Ls H (Z i) lam) (10.41 * l ^ (11 / 7 : ℝ)) (exp (-(A * l))) 0.3842
    (by positivity) (fun i _ => aS_nonneg hA0 _ _) (fun i hi => bS_nonneg hA0 (hZH i hi) hLH)
    hbi hasum hbsum
  refine lt_of_le_of_lt hb ?_
  have he1 : exp (-(A * l)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hsq : exp (-(A * l)) ^ 2 = exp (-(2 * A) * l) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hp0 : 0 ≤ l ^ (11 / 7 : ℝ) := rpow_nonneg hl0.le _
  have hc8 := LeanLab.ExceptionalSet.Pintz2018Reduction.case8_A (A := A) (l := l) hA hl0 hl1
  have : 10.41 * l ^ (11 / 7 : ℝ) * (2 * exp (-(A * l)) + 0.3842) ≤
      2.87 * 10.4 * l ^ (11 / 7 : ℝ) := by nlinarith [(exp_pos (-(A * l))).le]
  rw [hsq]
  linarith

/-- Case 8 at `A''`, an instance of `case8_closes_gen`, CONDITIONAL ON the same inputs. -/
theorem case8_closes2 {I : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {H Ls ε : ℝ} {i1 : κ}
    {j1 : ι} (hLH : Ls ≤ H) (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H) (hi1 : i1 ∈ I)
    (hj1 : j1 ∈ Z i1) (hsingle : ∀ i ∈ I, ∀ j ∈ Z i, lam j < Ls → i = i1 ∧ j = j1)
    (hl0 : 0 < lam j1) (hl1 : lam j1 ≤ 0.04) (hε : ε ≤ 1 / 100)
    (hLs1 : 3.96 ≤ Ls) (hLs2 : (12 / 11 - ε) * log (1 / lam j1) ≤ Ls)
    (h932a : ∑ i ∈ I, KS (8 / 3) Ls (Z i) lam ≤ 10.4 + exp (-(8 / 3 * Ls)))
    (h932b : ∀ i ∈ I, KS 2 Ls (Z i) lam ≤ 10.4 + exp (-(2 * Ls))) :
    ∑ i ∈ I, (aS A2 Ls (Z i) lam + bS A2 Ls H (Z i) lam) ^ 2 < 1 :=
  case8_closes_gen (by rw [A2_eq]; norm_num) hLH hZH hi1 hj1 hsingle hl0 hl1 hε hLs1 hLs2
    h932a h932b

/-- Vacuity instance for `case8_closes2`: one zero at `λ₁ = e^{-4} ≤ 0.04`, `Λ* = H = 5`,
`ε = 0`, so `(12/11) log(1/λ₁) = 48/11 ≤ 5`. -/
theorem case8_closes2_vacuity :
    ∑ _i ∈ ({0} : Finset ℕ), (aS A2 5 ({0} : Finset ℕ) (fun _ => exp (-4)) +
      bS A2 5 5 ({0} : Finset ℕ) (fun _ => exp (-4))) ^ 2 < 1 := by
  have hl : exp (-4 : ℝ) ≤ 0.04 := by
    have h1 := LeanLab.Pintz2018.expneg_upper 4 (by norm_num)
    simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
    norm_num at h1
    linarith
  have hlog : log (1 / exp (-4 : ℝ)) = 4 := by rw [one_div, ← exp_neg, log_exp]; norm_num
  have h4 : exp (-4 : ℝ) < 5 := by linarith
  have := case8_closes2 (ι := ℕ) (κ := ℕ) (I := {0}) (Z := fun _ => {0})
    (lam := fun _ => exp (-4)) (H := 5) (Ls := 5) (ε := 0) (i1 := 0) (j1 := 0) le_rfl
    (by intro _ _ _ _; linarith) (by simp) (by simp) (by intro i hi j hj _; simp_all)
    (exp_pos _) hl (by norm_num) (by norm_num) (by rw [hlog]; norm_num)
    (by
      simp only [KS, sum_singleton]
      rw [max_eq_right h4.le]
      linarith [exp_pos (-(8 / 3 * (5 : ℝ)))])
    (by
      intro i _
      simp only [KS, sum_singleton]
      rw [max_eq_right h4.le]
      linarith [exp_pos (-(2 * (5 : ℝ)))])
  simpa using this

end Cases

/-! ### Theorem 1 at the exponent `899/1249` -/

open LeanLab.ExceptionalSet.Pintz2018Reduction in
/-- `C Y^β ≤ c Y^α` for all large natural `Y`, when `β < α` and `c > 0`. PROVED, no input. -/
theorem absorb {β α : ℝ} (hβα : β < α) (C c : ℝ) (hc : 0 < c) :
    ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → C * (Y : ℝ) ^ β ≤ c * (Y : ℝ) ^ α := by
  have ht : Filter.Tendsto (fun Y : ℕ => |C| * (Y : ℝ) ^ (-(α - β))) Filter.atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < α - β)).comp
      tendsto_natCast_atTop_atTop).const_mul |C|
    simpa using this
  obtain ⟨Y2, hY2⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
  refine ⟨Y2, fun Y hY => ?_⟩
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hs := hY2 Y hY.le
  have hsplit : (Y : ℝ) ^ β = (Y : ℝ) ^ α * (Y : ℝ) ^ (-(α - β)) := by
    rw [← rpow_add hYpos]; ring_nf
  have hYa : 0 < (Y : ℝ) ^ α := rpow_pos_of_pos hYpos _
  calc C * (Y : ℝ) ^ β ≤ |C| * (Y : ℝ) ^ β :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (rpow_nonneg hYpos.le _)
    _ = (|C| * (Y : ℝ) ^ (-(α - β))) * (Y : ℝ) ^ α := by rw [hsplit]; ring
    _ ≤ c * (Y : ℝ) ^ α := mul_le_mul_of_nonneg_right hs.le hYa.le

open LeanLab.ExceptionalSet.Pintz2018Reduction in
/-- The reduction of `Pintz2018Reduction.pintz_of_inputs` with a general target exponent.
CONDITIONAL ON Theorem B, `TheoremBInput`, and the non-Siegel count at level `ϑ`,
`NonSiegelInput`. Plain math: if `E(Y) < Y^{0.601}` in the Siegel case, the non-Siegel blocks of
`(Y/2, Y]` hold at most `C Y^{1-ϑ}` exceptions, `0.601 < α` and `1 - ϑ < α`, then
`E(X) < X^α` for all large `X`. -/
theorem pintz_of_inputs_gen {Siegel : ℕ → Prop} {ϑ C α : ℝ} (hα : 0.601 < α) (hϑ : 1 - ϑ < α)
    (hB : TheoremBInput Siegel) (hA : NonSiegelInput Siegel ϑ C) :
    LeanLab.ExceptionalSet.EventuallyBelow α := by
  have h := eventually_lt_of_littleO Exc (α := α) (by linarith) (fun c hc => by
    obtain ⟨Y1, hY1⟩ := hB
    obtain ⟨Y2, hY2⟩ := hA
    obtain ⟨Y3, hY3⟩ := absorb (β := 0.601) hα 1 c hc
    obtain ⟨Y4, hY4⟩ := absorb hϑ C c hc
    refine ⟨max (max Y1 Y2) (max Y3 Y4), fun Y hY => ?_⟩
    have h1 : Y1 < Y := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hY
    have h2 : Y2 < Y := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hY
    have h3 : Y3 < Y := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hY
    have h4 : Y4 < Y := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hY
    by_cases hS : Siegel Y
    · have hE := hY1 Y h1 hS
      have hDE : (D Exc Y : ℝ) ≤ LeanLab.ExceptionalSet.E Y := by
        rw [E_eq_T]; exact_mod_cast D_le_T Exc Y
      have := hY3 Y h3
      linarith
    · have := hY2 Y h2 hS
      have := hY4 Y h4
      linarith)
  obtain ⟨X0, hX0⟩ := h
  exact ⟨X0, fun X hX => by rw [E_eq_T]; exact hX0 X hX⟩

open LeanLab.ExceptionalSet.Pintz2018Reduction in
/-- **Theorem 1 at the exponent `899/1249 = 0.719776...`, rounded up to `0.71978`.**
CONDITIONAL ON Theorem B and `NonSiegelInput` at `ϑ'' = 1/A'' = 350/1249`, the level that
`case7_closes2`, `cases1to6_closes2` and `case8_closes2` support. The step from those closures,
`S₀ ≤ 1 - c₀`, to `NonSiegelInput` is NOT formalized, and Case 7 rests on the LAB
RECONSTRUCTION `Case7AtLambda1`. This is at most a conditional observation that Pintz's own
printed margin allows a slightly smaller exponent than `0.72`; it is not a new record, since
Zhao 2025, arXiv 2511.05631, claims `7/10`.

Plain math: if `E(Y) < Y^{0.601}` in the Siegel case and the non-Siegel blocks hold at most
`C Y^{899/1249}` exceptions, then `E(X) < X^{0.71978}` for all large `X`. -/
theorem pintz_slack2 {Siegel : ℕ → Prop} {C : ℝ} (hB : TheoremBInput Siegel)
    (hA : NonSiegelInput Siegel (1 / A2) C) : LeanLab.ExceptionalSet.EventuallyBelow 0.71978 :=
  pintz_of_inputs_gen (by norm_num) (by rw [A2_eq]; norm_num) hB hA

open LeanLab.ExceptionalSet.Pintz2018Reduction in
/-- Every exponent above `1 - ϑ'' = 899/1249`, under the same CONDITIONAL inputs. -/
theorem pintz_slack2_all {Siegel : ℕ → Prop} {C α : ℝ} (hα : 899 / 1249 < α)
    (hB : TheoremBInput Siegel) (hA : NonSiegelInput Siegel (1 / A2) C) :
    LeanLab.ExceptionalSet.EventuallyBelow α :=
  pintz_of_inputs_gen (by linarith) (by rw [A2_eq]; norm_num; linarith) hB hA

open LeanLab.ExceptionalSet.Pintz2018Reduction in
/-- Vacuity, partial: each input of `pintz_slack2` is satisfiable on its own, `TheoremBInput`
with `Siegel` never true, `NonSiegelInput` with `Siegel` always true. Their joint
satisfiability for one `Siegel` is the content of Pintz's theorem and is not shown here. -/
theorem pintz_slack2_vacuity :
    TheoremBInput (fun _ => False) ∧ NonSiegelInput (fun _ => True) (1 / A2) 0 :=
  ⟨vacuity_theoremB, ⟨0, fun _ _ h => absurd trivial h⟩⟩

end LeanLab.ExceptionalSet.Pintz2018Slack2
