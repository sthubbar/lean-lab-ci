/-
Tao 2012, Every odd number greater than 1 is the sum of at most five primes, arXiv 1201.6656v4,
Math. Comp. 83 (2014). Unit U-1584, run PC 20261029T0804Z-25466, track T1 STATE, paper P0007.

Theorem 1.3 (Exponential sum estimate), page 5 of the v4 PDF, displays (1.9) to (1.12), for the
smoothed sum `S_{η₀,q₀}(x, α)` with the cutoff `η₀(t) := 4 (log 2 - |log 2t|)₊` of (1.7), page 4.
Read 2026-10-29 from papers/P0007.pdf page 5, rendered with pdftoppm, and checked a second time
against the LaTeX of arxiv.org/html/1201.6656. Both the PDF and the HTML call it Theorem 1.3.

Statement, as printed. Let `x ≥ 10^20` be real, and let `4α = a/q + β` for some natural number
`100 ≤ q ≤ x/100` with `(a, q) = 1` and some `β ∈ [-1/q², 1/q²]`. Let `q₀` be a natural number all
of whose prime factors are at most `√x`. Then
  (1.9)  |S| ≤ (0.14 x/√q + 0.64 x/√(x/q) + 0.15 x^{4/5}) log x (log x + 11.3);
  (1.10) if q ≤ x^{1/3}: |S| ≤ 0.5 (x/q) log 2x (log 2x + 15) + 0.31 (x/√q) log q (log q + 8.9);
  (1.11) if q ≥ x^{2/3}: |S| ≤ 3.12 (x/(x/q)) log 2x (log q + 8)
                               + 1.19 (x/√(x/q)) log(x/q) (log(x/q) + 2.3);
  (1.12) if q ≥ x^{2/3} and a = ±1: |S| ≤ 9.73 (x/(x/q)²) log² x
                               + 1.2 (x/√(x/q)) log(x/q) (log(x/q) + 2.4).

Each display is a `def ... : Prop`, to be passed as a hypothesis; nothing here is assumed with
`sorry`. Reused definitions: `Prop84.η₀` for (1.7) and `Decomp1555.S` for the sum (4.1).
`Prop84.η₀` uses Mathlib's `Real.log`, which is `log |t|` and `log 0 = 0`, so it differs from the
paper's cutoff at `t ≤ 0`; `S_eq_pos` shows this does not change `S`, because `S` only evaluates
the cutoff at `n/x` with `n ≥ 1`, `x > 0`, the term `n = 0` carrying `Λ 0 = 0`.

AI-written Lean code, Claude, 2026-10-29. Checked only by the Lean kernel.
Binary Goldbach is OPEN; this file states an input of Tao's five primes theorem.
-/
import Mathlib
import LeanLab.Tao2012.Prop84
import LeanLab.Tao2012.Eta1
import LeanLab.Tao2012.Decomp1555a

namespace LeanLab.Tao2012.State1584

open Real

/-- The cutoff `η₀` of (1.7), the lab's existing definition from Prop84.lean. -/
noncomputable abbrev η₀ : ℝ → ℝ := LeanLab.Tao2012.Prop84.η₀

/-- The smoothed sum `S_{η,q₀}(x, α) = ∑ₙ Λ(n) e(αn) 1_{(n,q₀)=1} η(n/x)`, page 4, the lab's
existing definition from Decomp1555a.lean, summing `n ≤ x`, which holds the support of `η₀`. -/
noncomputable abbrev S : (ℝ → ℝ) → ℕ → ℝ → ℝ → ℂ := LeanLab.Tao2012.Decomp1555.S

/-! ## The hypotheses of Theorem 1.3 -/

/-- The common hypotheses of Theorem 1.3, page 5: `x ≥ 10^20`, `4α = a/q + β`,
`100 ≤ q ≤ x/100`, `(a, q) = 1`, `β ∈ [-1/q², 1/q²]`, every prime factor of `q₀` at most `√x`. -/
def Hyp (x α β : ℝ) (a : ℤ) (q q₀ : ℕ) : Prop :=
  (10 : ℝ) ^ 20 < x ∧ 4 * α = (a : ℝ) / q + β ∧ 100 ≤ q ∧ (q : ℝ) ≤ x / 100 ∧
    Int.gcd a q = 1 ∧ -1 / (q : ℝ) ^ 2 ≤ β ∧ β ≤ 1 / (q : ℝ) ^ 2 ∧
    ∀ p : ℕ, p.Prime → p ∣ q₀ → (p : ℝ) ≤ sqrt x

/-! ## The four right hand sides, constants as printed on page 5 -/

/-- Right side of (1.9). -/
noncomputable def B1_9 (x q : ℝ) : ℝ :=
  (0.14 * (x / sqrt q) + 0.64 * (x / sqrt (x / q)) + 0.15 * x ^ ((4 : ℝ) / 5)) *
    log x * (log x + 11.3)

/-- Right side of (1.10). -/
noncomputable def B1_10 (x q : ℝ) : ℝ :=
  0.5 * (x / q) * log (2 * x) * (log (2 * x) + 15) +
    0.31 * (x / sqrt q) * log q * (log q + 8.9)

/-- Right side of (1.11). -/
noncomputable def B1_11 (x q : ℝ) : ℝ :=
  3.12 * (x / (x / q)) * log (2 * x) * (log q + 8) +
    1.19 * (x / sqrt (x / q)) * log (x / q) * (log (x / q) + 2.3)

/-- Right side of (1.12). -/
noncomputable def B1_12 (x q : ℝ) : ℝ :=
  9.73 * (x / (x / q) ^ 2) * log x ^ 2 +
    1.2 * (x / sqrt (x / q)) * log (x / q) * (log (x / q) + 2.4)

/-! ## The SEALED statements -/

/-- (1.9), page 5. -/
def Eq1_9 : Prop := ∀ (x α β : ℝ) (a : ℤ) (q q₀ : ℕ), Hyp x α β a q q₀ →
  ‖S η₀ q₀ x α‖ ≤ B1_9 x q

/-- (1.10), page 5: the refinement for `q ≤ x^{1/3}`. -/
def Eq1_10 : Prop := ∀ (x α β : ℝ) (a : ℤ) (q q₀ : ℕ), Hyp x α β a q q₀ →
  (q : ℝ) ≤ x ^ ((1 : ℝ) / 3) → ‖S η₀ q₀ x α‖ ≤ B1_10 x q

/-- (1.11), page 5: the refinement for `q ≥ x^{2/3}`. -/
def Eq1_11 : Prop := ∀ (x α β : ℝ) (a : ℤ) (q q₀ : ℕ), Hyp x α β a q q₀ →
  x ^ ((2 : ℝ) / 3) ≤ (q : ℝ) → ‖S η₀ q₀ x α‖ ≤ B1_11 x q

/-- (1.12), page 5: the further refinement for `q ≥ x^{2/3}` and `a = ±1`. -/
def Eq1_12 : Prop := ∀ (x α β : ℝ) (a : ℤ) (q q₀ : ℕ), Hyp x α β a q q₀ →
  x ^ ((2 : ℝ) / 3) ≤ (q : ℝ) → (a = 1 ∨ a = -1) → ‖S η₀ q₀ x α‖ ≤ B1_12 x q

/-- Theorem 1.3, page 5: all four displays. -/
def Theorem1_3 : Prop := Eq1_9 ∧ Eq1_10 ∧ Eq1_11 ∧ Eq1_12

/-! ## VACUITY instances: the hypotheses of each statement can hold -/

theorem prime_dvd_one_false : ∀ p : ℕ, p.Prime → p ∣ 1 → (p : ℝ) ≤ sqrt (10 ^ 30) := by
  intro p hp h
  exact absurd (Nat.dvd_one.mp h) hp.one_lt.ne'

/-- `x = 10^30`, `q = 100`, `a = 1`, `β = 0`, `α = 1/400`, `q₀ = 1` satisfy the hypotheses. -/
theorem hyp_small : Hyp (10 ^ 30) (1 / 400) 0 1 100 1 := by
  refine ⟨by norm_num, by norm_num, le_refl _, by norm_num, by norm_num, by norm_num, by norm_num,
    prime_dvd_one_false⟩

/-- `x = 10^30`, `q = 10^20`, `a = 1`, `β = 0`, `α = 1/(4·10^20)`, `q₀ = 1`. -/
theorem hyp_large : Hyp (10 ^ 30) (1 / (4 * 10 ^ 20)) 0 1 (10 ^ 20) 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, prime_dvd_one_false⟩

theorem cube_root : ((10 : ℝ) ^ 30) ^ ((1 : ℝ) / 3) = 10 ^ 10 := by
  have h : ((10 : ℝ) ^ 30) = ((10 : ℝ) ^ 10) ^ ((3 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; norm_num
  rw [h, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem two_thirds : ((10 : ℝ) ^ 30) ^ ((2 : ℝ) / 3) = 10 ^ 20 := by
  have h : ((10 : ℝ) ^ 30) = ((10 : ℝ) ^ 10) ^ ((3 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; norm_num
  rw [h, ← Real.rpow_mul (by norm_num)]
  rw [show ((3 : ℕ) : ℝ) * (2 / 3) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- VACUITY for (1.9) and (1.10): the hypotheses of both hold at the `hyp_small` instance. -/
theorem vacuity_1_10 :
    Hyp (10 ^ 30) (1 / 400) 0 1 100 1 ∧ ((100 : ℕ) : ℝ) ≤ ((10 : ℝ) ^ 30) ^ ((1 : ℝ) / 3) := by
  refine ⟨hyp_small, ?_⟩
  rw [cube_root]; norm_num

/-- VACUITY for (1.11) and (1.12): the hypotheses of both hold at the `hyp_large` instance,
with `a = 1`. -/
theorem vacuity_1_12 :
    Hyp (10 ^ 30) (1 / (4 * 10 ^ 20)) 0 1 (10 ^ 20) 1 ∧
      ((10 : ℝ) ^ 30) ^ ((2 : ℝ) / 3) ≤ ((10 ^ 20 : ℕ) : ℝ) ∧ ((1 : ℤ) = 1 ∨ (1 : ℤ) = -1) := by
  refine ⟨hyp_large, ?_, Or.inl rfl⟩
  rw [two_thirds]; norm_num

/-- The four bounds are finite positive numbers at the instances, so no statement is
`‖S‖ ≤ 0` or another degenerate inequality there. -/
theorem B1_10_pos : 0 < B1_10 (10 ^ 30) 100 := by
  unfold B1_10
  have h1 : 0 < log (2 * (10 : ℝ) ^ 30) := log_pos (by norm_num)
  have h2 : 0 < log (100 : ℝ) := log_pos (by norm_num)
  have h3 : 0 < sqrt (100 : ℝ) := sqrt_pos.mpr (by norm_num)
  positivity

theorem B1_9_pos : 0 < B1_9 (10 ^ 30) 100 := by
  unfold B1_9
  have h1 : 0 < log ((10 : ℝ) ^ 30) := log_pos (by norm_num)
  have h3 : 0 < sqrt (100 : ℝ) := sqrt_pos.mpr (by norm_num)
  have h4 : 0 < sqrt ((10 : ℝ) ^ 30 / 100) := sqrt_pos.mpr (by norm_num)
  positivity

theorem B1_12_pos : 0 < B1_12 (10 ^ 30) (10 ^ 20) := by
  unfold B1_12
  have h1 : 0 < log ((10 : ℝ) ^ 30 / 10 ^ 20) := log_pos (by norm_num)
  have h4 : 0 < sqrt ((10 : ℝ) ^ 30 / 10 ^ 20) := sqrt_pos.mpr (by norm_num)
  have h5 : 0 < log ((10 : ℝ) ^ 30) := log_pos (by norm_num)
  positivity

theorem B1_11_pos : 0 < B1_11 (10 ^ 30) (10 ^ 20) := by
  unfold B1_11
  have h1 : 0 < log ((10 : ℝ) ^ 30 / 10 ^ 20) := log_pos (by norm_num)
  have h4 : 0 < sqrt ((10 : ℝ) ^ 30 / 10 ^ 20) := sqrt_pos.mpr (by norm_num)
  have h5 : 0 < log (2 * (10 : ℝ) ^ 30) := log_pos (by norm_num)
  have h6 : 0 < log ((10 : ℝ) ^ 20) := log_pos (by norm_num)
  positivity

/-! ## Elementary facts about η₀, (1.7) and the sentence after it on page 5 -/

theorem η₀_nonneg (t : ℝ) : 0 ≤ η₀ t := by
  show 0 ≤ 4 * max (log 2 - |log (2 * t)|) 0
  have := le_max_right (log 2 - |log (2 * t)|) 0
  linarith

/-- Support, left end: `η₀ t = 0` for `0 < t ≤ 1/4`. -/
theorem η₀_zero_left {t : ℝ} (h0 : 0 < t) (h : t ≤ 1 / 4) : η₀ t = 0 := by
  show 4 * max (log 2 - |log (2 * t)|) 0 = 0
  have h1 : log (2 * t) ≤ log (1 / 2) := log_le_log (by positivity) (by linarith)
  rw [one_div, log_inv] at h1
  have : log 2 ≤ |log (2 * t)| := by rw [abs_of_nonpos (by linarith [log_pos (by norm_num : (1:ℝ) < 2)])]; linarith
  rw [max_eq_right (by linarith)]; ring

/-- Support, right end: `η₀ t = 0` for `t ≥ 1`. -/
theorem η₀_zero_right {t : ℝ} (h : 1 ≤ t) : η₀ t = 0 := by
  show 4 * max (log 2 - |log (2 * t)|) 0 = 0
  have h1 : log 2 ≤ log (2 * t) := log_le_log (by norm_num) (by linarith)
  have : log 2 ≤ |log (2 * t)| := le_trans h1 (le_abs_self _)
  rw [max_eq_right (by linarith)]; ring

/-- The lab's `η₀` is the paper's cutoff only for `t > 0`: Mathlib's `log` is `log |t|`, so
`η₀ (-1/2) = 4 log 2`. Harmless inside `S`, see `S_eq_pos`. -/
theorem η₀_neg_half : η₀ (-1 / 2) = 4 * log 2 := by
  show 4 * max (log 2 - |log (2 * (-1 / 2))|) 0 = 4 * log 2
  norm_num
  exact (log_pos (by norm_num)).le

/-- The paper's cutoff, zero off the positive reals. -/
noncomputable def η₀pos (t : ℝ) : ℝ := if 0 < t then η₀ t else 0

/-- `S` does not see the values of the cutoff at `t ≤ 0`: for `x > 0` the sum with the lab's
`η₀` equals the sum with `η₀pos`. -/
theorem S_eq_pos {x : ℝ} (hx : 0 < x) (q₀ : ℕ) (α : ℝ) : S η₀ q₀ x α = S η₀pos q₀ x α := by
  unfold S LeanLab.Tao2012.Decomp1555.S
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold LeanLab.Tao2012.Decomp1555.coef
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : 0 < (n : ℝ) / x := div_pos (by exact_mod_cast hn) hx
    simp [η₀pos, this]

theorem η₀_contOn : ContinuousOn η₀ (Set.Icc (1 / 4) 1) := by
  show ContinuousOn (fun t => 4 * max (log 2 - |log (2 * t)|) 0) _
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.sup _ continuousOn_const
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.abs
  apply ContinuousOn.log (continuousOn_const.mul continuousOn_id)
  intro t ht
  simp only [Set.mem_Icc] at ht
  have : 0 < t := by linarith [ht.1]
  exact mul_ne_zero two_ne_zero this.ne'

/-- Unit mass, page 5: `∫_{1/4}^{1} η₀ = 1`, and `η₀` vanishes on `(0, 1/4]` and `[1, ∞)`. -/
theorem η₀_mass : ∫ t in (1 / 4 : ℝ)..1, η₀ t = 1 := by
  have hl2 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have hl12 : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
  have hl14 : log (1 / 4 : ℝ) = -(2 * log 2) := by rw [one_div, log_inv, hl2]
  have hi : ∀ a b : ℝ, 1 / 4 ≤ a → b ≤ 1 → a ≤ b →
      IntervalIntegrable η₀ MeasureTheory.volume a b := by
    intro a b ha hb hab
    apply ContinuousOn.intervalIntegrable
    apply η₀_contOn.mono
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha hb
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hi _ _ le_rfl (by norm_num) (by norm_num)) (hi _ _ (by norm_num) le_rfl (by norm_num))]
  have e1 : ∫ t in (1 / 4 : ℝ)..(1 / 2), η₀ t = ∫ t in (1 / 4 : ℝ)..(1 / 2), (4 * log 4 + 4 * log t) := by
    apply Eta1.integral_eq_on (by norm_num)
    intro t h1 h2
    show LeanLab.Tao2012.Prop84.η₀ t = _
    rw [LeanLab.Tao2012.Prop84.η₀_left h1 h2, log_mul (by norm_num) (by linarith)]; ring
  have e2 : ∫ t in (1 / 2 : ℝ)..1, η₀ t = ∫ t in (1 / 2 : ℝ)..1, (-4 * log t) := by
    apply Eta1.integral_eq_on (by norm_num)
    intro t h1 h2
    exact LeanLab.Tao2012.Prop84.η₀_right h1 h2
  have i1 : ∫ t in (1 / 4 : ℝ)..(1 / 2), (4 * log 4 + 4 * log t) = 2 * log 2 - 1 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_log').const_mul 4),
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul (4 : ℝ) (fun t : ℝ => log t), integral_log,
      hl12, hl14, hl2, smul_eq_mul]
    ring
  have i2 : ∫ t in (1 / 2 : ℝ)..1, (-4 * log t) = 2 - 2 * log 2 := by
    rw [intervalIntegral.integral_const_mul (-4 : ℝ) (fun t : ℝ => log t), integral_log,
      hl12, log_one]
    ring
  rw [e1, e2, i1, i2]
  ring

/-! ## Sanity: Theorem 1.3 unpacks into the four displays -/

theorem eq1_9_of (h : Theorem1_3) : Eq1_9 := h.1
theorem eq1_12_of (h : Theorem1_3) : Eq1_12 := h.2.2.2

end LeanLab.Tao2012.State1584

#print axioms LeanLab.Tao2012.State1584.prime_dvd_one_false
#print axioms LeanLab.Tao2012.State1584.hyp_small
#print axioms LeanLab.Tao2012.State1584.hyp_large
#print axioms LeanLab.Tao2012.State1584.cube_root
#print axioms LeanLab.Tao2012.State1584.two_thirds
#print axioms LeanLab.Tao2012.State1584.vacuity_1_10
#print axioms LeanLab.Tao2012.State1584.vacuity_1_12
#print axioms LeanLab.Tao2012.State1584.B1_9_pos
#print axioms LeanLab.Tao2012.State1584.B1_10_pos
#print axioms LeanLab.Tao2012.State1584.B1_11_pos
#print axioms LeanLab.Tao2012.State1584.B1_12_pos
#print axioms LeanLab.Tao2012.State1584.η₀_nonneg
#print axioms LeanLab.Tao2012.State1584.η₀_zero_left
#print axioms LeanLab.Tao2012.State1584.η₀_zero_right
#print axioms LeanLab.Tao2012.State1584.η₀_neg_half
#print axioms LeanLab.Tao2012.State1584.S_eq_pos
#print axioms LeanLab.Tao2012.State1584.η₀_contOn
#print axioms LeanLab.Tao2012.State1584.η₀_mass
#print axioms LeanLab.Tao2012.State1584.eq1_9_of
#print axioms LeanLab.Tao2012.State1584.eq1_12_of
