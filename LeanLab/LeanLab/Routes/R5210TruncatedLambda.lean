import Mathlib

/-!
# R-5210, T3 MOONSHOT: the truncated von Mangoldt split of the Goldbach count

Unit U-6451, CLOUD 20261020T1318Z-cloud43. AI wrote this file.

Route: split `Λ = Λ_R + E` with the Goldston-Yıldırım truncated divisor sum
`Λ_R(n) = Σ_{d ∣ n, d ≤ R} μ(d) log(R/d)`. For every even `N`,
`Σ_{a+b=N} Λ(a)Λ(b) = 2 Σ Λ(a)Λ_R(b) - Σ Λ_R(a)Λ_R(b) + Σ E(a)E(b)`, `conv_split`.
The first two sums are fixed by sieve data of level `R`: `Λ_R` is a fixed arithmetic function,
and `Σ f(a)Λ_R(N - a)` depends on `f` only through the residue sums
`Σ_{a < N, d ∣ N - a} f(a)` for `d ≤ R`, `cross_eq_data` and `cross_eq_of_same_data`. Numerically
both are `𝔖(N) N (1 + o(1))` from `R = N^{1/2}` on, Routes/numerics/r5210_*_U6451.out. So binary
Goldbach for `N` is exactly the statement that the self correlation `Σ E(a)E(N - a)` of the part of
`Λ` that level `R` data cannot see is above `-𝔖(N) N`; and any `g` with the same level `R` data as
`Λ` and no Goldbach pair of `N`, as built in R-5062, has `Σ E_g E_g = Σ Λ_RΛ_R - 2 Σ ΛΛ_R`,
`invisible_carries_all`. Also `lamR_eq_vonMangoldt`: `Λ_R = Λ` on `[2, R]`, so `E` vanishes there.

KNOWN mathematics in substance: Goldston-Yıldırım, correlations of `Λ_R`, arXiv math/0111212
and later parts; Goldston-Yıldırım, Illinois J. Math. 39 (1995), truncated `Λ_Q` in Goldbach
averages; Matomäki-Radziwiłł-Tao, arXiv 1707.01315, correlations of `Λ` with Goldbach sums.
Nothing claimed new. A map entry, not progress on Goldbach, which is OPEN.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace LeanLab.Routes.R5210
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The truncated von Mangoldt function `Λ_R(n) = Σ_{d ∣ n, d ≤ R} μ(d) log(R/d)`. -/
noncomputable def lamR (R : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ R), (μ d : ℝ) * Real.log (R / d)

/-- The additive convolution `Σ_{a ≤ N} u(a) v(N - a)`. -/
noncomputable def conv (u v : ℕ → ℝ) (N : ℕ) : ℝ := ∑ a ∈ range (N + 1), u a * v (N - a)

/-- Level `R` data of `f` at `N`: the sums `Σ_{a < N, d ∣ N - a} f(a)`. -/
noncomputable def data (f : ℕ → ℝ) (N d : ℕ) : ℝ := ∑ a ∈ range N with d ∣ N - a, f a

lemma sum_moebius_divisors {n : ℕ} (hn : n ≠ 1) : ∑ d ∈ n.divisors, (μ d : ℝ) = 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n) (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [coe_mul_zeta_apply, one_apply_ne hn] at h
  simpa [intCoe_apply] using h

/-- **`Λ_R = Λ` on `[2, R]`.** -/
theorem lamR_eq_vonMangoldt {R : ℝ} {n : ℕ} (hn : 2 ≤ n) (hnR : (n : ℝ) ≤ R) :
    lamR R n = Λ n := by
  have hR : 0 < R := lt_of_lt_of_le (by exact_mod_cast (show 0 < n by omega)) hnR
  have hfilt : (n.divisors.filter fun d : ℕ => (d : ℝ) ≤ R) = n.divisors := by
    apply filter_true_of_mem
    intro d hd
    exact le_trans (by exact_mod_cast Nat.divisor_le hd) hnR
  unfold lamR
  rw [hfilt]
  have hsplit : ∀ d ∈ n.divisors, (μ d : ℝ) * Real.log (R / d) =
      Real.log R * (μ d : ℝ) - (μ d : ℝ) * Real.log d := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd
      exact_mod_cast this.ne'
    rw [Real.log_div hR.ne' hd0]; ring
  rw [sum_congr rfl hsplit, sum_sub_distrib, ← mul_sum, sum_moebius_divisors (by omega)]
  have := sum_moebius_mul_log_eq (n := n)
  simp only [mul_zero, zero_sub]
  rw [neg_eq_iff_eq_neg]
  simp only [ArithmeticFunction.log_apply] at this
  convert this using 1

lemma lamR_zero (R : ℝ) : lamR R 0 = 0 := by simp [lamR]

/-- `Σ_{a ≤ N} u(a) v(N - a)` is symmetric. -/
lemma conv_comm (u v : ℕ → ℝ) (N : ℕ) : conv u v N = conv v u N := by
  unfold conv
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro a ha
  have := mem_range.mp ha
  rw [show N + 1 - 1 - a = N - a by omega, show N - (N - a) = a by omega, mul_comm]

lemma conv_sub_left (u v w : ℕ → ℝ) (N : ℕ) :
    conv (fun n => u n - v n) w N = conv u w N - conv v w N := by
  unfold conv; rw [← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring

lemma conv_sub_right (u v w : ℕ → ℝ) (N : ℕ) :
    conv w (fun n => u n - v n) N = conv w u N - conv w v N := by
  unfold conv; rw [← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring

/-- **The split.** With `E = f - Λ_R`,
`Σ f(a) f(N - a) = 2 Σ f(a) Λ_R(N - a) - Σ Λ_R(a) Λ_R(N - a) + Σ E(a) E(N - a)`. -/
theorem conv_split (f : ℕ → ℝ) (R : ℝ) (N : ℕ) :
    conv f f N = 2 * conv f (lamR R) N - conv (lamR R) (lamR R) N +
      conv (fun n => f n - lamR R n) (fun n => f n - lamR R n) N := by
  rw [conv_sub_left, conv_sub_right, conv_sub_right, conv_comm (lamR R) f N]
  ring

/-- **The cross term sees only level `R` data.**
`Σ_{a ≤ N} f(a) Λ_R(N - a) = Σ_{1 ≤ d ≤ N, d ≤ R} μ(d) log(R/d) Σ_{a < N, d ∣ N - a} f(a)`. -/
theorem cross_eq_data (f : ℕ → ℝ) (R : ℝ) (N : ℕ) :
    conv f (lamR R) N = ∑ d ∈ (Icc 1 N).filter (fun d : ℕ => (d : ℝ) ≤ R), (μ d : ℝ) * Real.log (R / d) * data f N d := by
  unfold conv
  rw [sum_range_succ, Nat.sub_self, lamR_zero, mul_zero, add_zero]
  have hdiv : ∀ a ∈ range N, lamR R (N - a) =
      ∑ d ∈ (Icc 1 N).filter (fun d : ℕ => (d : ℝ) ≤ R), if d ∣ N - a then (μ d : ℝ) * Real.log (R / d) else 0 := by
    intro a ha
    have ha' := mem_range.mp ha
    unfold lamR
    rw [← sum_filter]
    apply sum_congr
    · ext d
      simp only [mem_filter, Nat.mem_divisors, mem_Icc]
      constructor
      · rintro ⟨⟨hd, _⟩, hR⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) (by omega)⟩,
          hR⟩, hd⟩
      · rintro ⟨⟨_, hR⟩, hd⟩
        exact ⟨⟨hd, by omega⟩, hR⟩
    · intro _ _; rfl
  rw [sum_congr rfl fun a ha => by rw [hdiv a ha]]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  unfold data
  rw [sum_filter, mul_sum]
  apply sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- Two functions with the same level `R` data at `N` have the same cross term with `Λ_R`. -/
theorem cross_eq_of_same_data {f g : ℕ → ℝ} {R : ℝ} {N : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ N → (d : ℝ) ≤ R → data f N d = data g N d) :
    conv f (lamR R) N = conv g (lamR R) N := by
  rw [cross_eq_data, cross_eq_data]
  apply sum_congr rfl
  intro d hd
  simp only [mem_filter, mem_Icc] at hd
  rw [h d hd.1.1 hd.1.2 hd.2]

/-- **The invisible part carries all of it.** If `g` has the level `R` data of `f` at `N` and
`Σ g(a) g(N - a) = 0`, then the self correlation of `E_g = g - Λ_R` is
`Σ Λ_R Λ_R - 2 Σ f Λ_R`, a quantity of level `R` data alone. -/
theorem invisible_carries_all {f g : ℕ → ℝ} {R : ℝ} {N : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ N → (d : ℝ) ≤ R → data f N d = data g N d) (hg : conv g g N = 0) :
    conv (fun n => g n - lamR R n) (fun n => g n - lamR R n) N =
      conv (lamR R) (lamR R) N - 2 * conv f (lamR R) N := by
  have := conv_split g R N
  rw [← cross_eq_of_same_data h] at this
  linarith

/-- Vacuity: `Λ_R(2) = Λ(2) = log 2` at `R = 2`, so the hypotheses of `lamR_eq_vonMangoldt` hold. -/
example : lamR 2 2 = Real.log 2 := by
  rw [lamR_eq_vonMangoldt le_rfl (by norm_num), vonMangoldt_apply_prime Nat.prime_two]
  norm_num

end LeanLab.Routes.R5210
