/-
Re-split of the two leaves `leaf_karLemma2_small` and `leaf_karLemma2_from_mvt` of
`LeanLab.ExceptionalSet.KarLemma2Split`, Lemma 2 of A. A. Karacuba, Trudy Mat. Inst. Steklov
112 (1971), p. 243-244, Vinogradov's estimate of a Weyl sum from a rational approximation of
one coefficient, Karacuba's reference [2], I. M. Vinogradov, the method of trigonometric
sums. Karacuba states Lemma 2 without proof; the steps below follow Vinogradov's method as
Karacuba himself runs it for `W(a)` on p. 245-247, displays (3) to (6).

Steps of the proof.
1. `karL2_shift`: PROVED. The shift `x ↦ x + yz`, `0 ≤ y, z ≤ M`, and averaging, display (3)
   of p. 245 in the form of `shift_average`, for the sum over `1 ≤ x ≤ P`.
2. `karL2_taylor`, `karL2_taylor_split`: PROVED. The binomial expansion
   `f(x + t) = Σ_s A_s(x) t^s`, `A_s(x) = Σ_j α_j C(j, s) x^{j-s}`, `karL2Coef`.
3. `karL2_holder_at`: PROVED. For each `x`, the two Holder steps, Lemma 4 a and b, and the
   geometric sums, display (5) and (6) of p. 246 through the proved `karW_display5_6` in degree
   `n + 1`: `|W(x)|^{4k²} ≤ (M+1)^{8k²-4k} J_k(0)² Π_{s=1}^{n+1} 𝔖_s(m A_s(x))`.
4. `karL2_reduce`: PROVED. Steps 1 to 3 together: `|S|` is at most the average over `x` of the
   `4k²`-th roots of these bounds plus `2M²`, for every `M` and every `k ≥ 1`.
5. `KarJ0Bound d`: the conclusion of the proved `karJ0_lemma1`, Lemma 1 for `J_k(0)` with
   `k = b_l`, in degree `d`. `karJ0Bound_of_lemma1`: PROVED from `KarLemma1` for `d ≥ 12`.
6. `leaf_karL2_core`: LEAF, HARD. The rest of Vinogradov's proof: the choice of `M` and of
   `k = b_l`, Lemma 1 through `KarJ0Bound (n+1)`, the sum over `x` of the products of the
   sums `𝔖_s` using the approximation of `α_r` and Lemma 3, and the final exponent
   arithmetic giving `ρ = τ/(3 n² l)`. It contains no exponential sum any more.
7. `leaf_karJ0_lowdeg`: LEAF, HARD. Lemma 1 for `J_k(0)` in the degrees `2 ≤ d ≤ 12`, which
   `KarLemma1` does not state below 12.
8. `karLemma2_from_mvt_steps`, `karLemma2_small_steps`: PROVED assemblies, with the exact
   types of `leaf_karLemma2_from_mvt` and `leaf_karLemma2_small`, checked by twins.

The case `n < 12`: the same chain reaches it. The only place where the degree restriction of
`KarLemma1` enters is the bound on `J_k(0)` in degree `n + 1`; for `n ≥ 11` it comes from
`KarLemma1`, for `n < 12` from `leaf_karJ0_lowdeg`. The core leaf is stated for every `n ≥ 1`.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KarLemma2Split
import LeanLab.ExceptionalSet.SPLIT_leaf_karW_display8

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Step 2: the Taylor coefficients -/

/-- The Taylor coefficient `A_s(x) = f^{(s)}(x)/s! = Σ_{j=1}^{n+1} α_j C(j, s) x^{j-s}` of
`f(x) = α_{n+1} x^{n+1} + ... + α_1 x`, Karacuba Lemma 2 p. 243, in the expansion of
`f(x + yz)` in powers of `yz` used by Vinogradov's shift, Karacuba p. 245 display (4). -/
noncomputable def karL2Coef (n : ℕ) (α : ℕ → ℝ) (x : ℝ) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n + 1), α j * (j.choose s : ℝ) * x ^ (j - s)

/-- Reindexing a sum over `1 ≤ s ≤ N` as a sum over `0 ≤ i < N`. -/
theorem karL2_sum_Icc_range {R : Type*} [AddCommMonoid R] (N : ℕ) (g : ℕ → R) :
    ∑ s ∈ Finset.Icc 1 N, g s = ∑ i ∈ Finset.range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- PROVED. The binomial expansion of `f(x + t)` in powers of `t`. -/
theorem karL2_taylor (n : ℕ) (α : ℕ → ℝ) (x t : ℝ) :
    ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x + t) ^ j =
      ∑ s ∈ Finset.range (n + 2), karL2Coef n α x s * t ^ s := by
  have h : ∀ j ∈ Finset.Icc 1 (n + 1), α j * (x + t) ^ j =
      ∑ s ∈ Finset.range (n + 2), α j * (j.choose s : ℝ) * x ^ (j - s) * t ^ s := by
    intro j hj
    have hj' : j + 1 ≤ n + 2 := by have := (Finset.mem_Icc.1 hj).2; omega
    rw [add_comm x t, add_pow, Finset.mul_sum, ← Finset.sum_range_add_sum_Ico _ hj']
    have h0 : ∑ s ∈ Finset.Ico (j + 1) (n + 2), α j * (j.choose s : ℝ) * x ^ (j - s) * t ^ s
        = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      have := (Finset.mem_Ico.1 hs).1
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [karL2Coef, Finset.sum_mul]

/-- PROVED. The expansion with the constant term apart, in the form of display (4):
`m f(x + t) = m A_0(x) + Σ_{s=1}^{n+1} m A_s(x) t^s`. -/
theorem karL2_taylor_split (n : ℕ) (m : ℝ) (α : ℕ → ℝ) (x t : ℝ) :
    m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x + t) ^ j =
      m * karL2Coef n α x 0 +
        ∑ s ∈ Finset.Icc 1 (n + 1), m * karL2Coef n α x s * t ^ s := by
  rw [karL2_taylor, Finset.sum_range_succ', karL2_sum_Icc_range, mul_add, Finset.mul_sum]
  simp only [pow_zero, mul_one]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-! ### Step 1: the shift `x ↦ x + yz` -/

/-- PROVED. Display (3) of Karacuba p. 245 for the sum over `1 ≤ x ≤ P`, Vinogradov's shift:
`S = (M+1)^{-2} Σ_x Σ_{y,z ≤ M} g(x + yz) + θ'`, `|θ'| ≤ 2M²`, from `shift_average`. -/
theorem karL2_shift (g : ℕ → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) (P M : ℕ) :
    ‖∑ x ∈ Finset.Icc 1 P, g x - (((M : ℂ) + 1) ^ 2)⁻¹ *
      ∑ x ∈ Finset.Icc 1 P, ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        g (x + y * z)‖ ≤ 2 * (M : ℝ) ^ 2 := by
  have h := shift_average g hg 1 P M
  have e1 : ∑ x ∈ Finset.Icc 1 P, g x = ∑ k ∈ Finset.range P, g (1 + k) := by
    rw [karL2_sum_Icc_range]
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
  have e2 : ∑ x ∈ Finset.Icc 1 P, ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        g (x + y * z) = ∑ k ∈ Finset.range P, ∑ y ∈ Finset.range (M + 1),
          ∑ z ∈ Finset.range (M + 1), g (1 + k + y * z) := by
    rw [karL2_sum_Icc_range]
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm k 1]
  rw [e1, e2]
  exact h

/-! ### Step 3: Holder, display (5) and (6), for each `x` -/

/-- PROVED. For each `x`, the sum `W(x) = Σ_{y,z ≤ M} e(m f(x + yz))` satisfies display (6)
of Karacuba p. 246 in degree `n + 1`, through the Taylor expansion and the proved
`karW_display5_6`: `|W(x)|^{4k²} ≤ (M+1)^{8k²-4k} J_k(0)² Π_{s=1}^{n+1} 𝔖_s(m A_s(x))`. -/
theorem karL2_holder_at (n m M k x : ℕ) (hk : 1 ≤ k) (α : ℕ → ℝ) :
    ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (((x + y * z : ℕ) : ℕ) : ℝ) ^ j)‖ ^ (4 * k ^ 2)
      ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 (n + 1) k M ^ 2 *
        ∏ s ∈ Finset.Icc 1 (n + 1), karSigma k M s ((m : ℝ) * karL2Coef n α x s) := by
  have h := karW_display5_6 (n + 1) M k hk ((m : ℝ) * karL2Coef n α x 0)
    (fun s => (m : ℝ) * karL2Coef n α x s)
  have e : ∀ y z : ℕ, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (((x + y * z : ℕ) : ℕ) : ℝ) ^ j)
      = eC ((m : ℝ) * karL2Coef n α x 0 + ∑ j ∈ Finset.Icc 1 (n + 1),
          (fun s => (m : ℝ) * karL2Coef n α x s) j * (((y * z : ℕ) : ℝ) ^ j)) := by
    intro y z
    congr 1
    rw [show (((x + y * z : ℕ) : ℕ) : ℝ) = (x : ℝ) + ((y * z : ℕ) : ℝ) by push_cast; ring]
    exact karL2_taylor_split n m α x _
  simp_rw [e]
  exact h

/-! ### Step 4: steps 1 to 3 together -/

/-- PROVED. Steps 1 to 3: for every `M` and every `k ≥ 1`,
`|S| ≤ (M+1)^{-2} Σ_{x=1}^P ((M+1)^{8k²-4k} J_k(0)² Π_s 𝔖_s(m A_s(x)))^{1/(4k²)} + 2M²`. -/
theorem karL2_reduce (n m P M k : ℕ) (hk : 1 ≤ k) (α : ℕ → ℝ) :
    ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ ≤
      (((M : ℝ) + 1) ^ 2)⁻¹ * ∑ x ∈ Finset.Icc 1 P,
        (((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 (n + 1) k M ^ 2 *
          ∏ s ∈ Finset.Icc 1 (n + 1), karSigma k M s ((m : ℝ) * karL2Coef n α x s))
          ^ (((4 * k ^ 2 : ℕ) : ℝ)⁻¹) + 2 * (M : ℝ) ^ 2 := by
  set g : ℕ → ℂ := fun x => eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j) with hgdef
  have hg : ∀ x, ‖g x‖ ≤ 1 := fun x => by rw [hgdef]; simp only; rw [norm_eC]
  have hsh := karL2_shift g hg P M
  set S := ∑ x ∈ Finset.Icc 1 P, g x
  set T := (((M : ℂ) + 1) ^ 2)⁻¹ * ∑ x ∈ Finset.Icc 1 P, ∑ y ∈ Finset.range (M + 1),
    ∑ z ∈ Finset.range (M + 1), g (x + y * z) with hT
  have hST : ‖S‖ ≤ ‖T‖ + 2 * (M : ℝ) ^ 2 := by
    have : ‖S‖ ≤ ‖S - T‖ + ‖T‖ := by
      calc ‖S‖ = ‖(S - T) + T‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have hinv : ‖(((M : ℂ) + 1) ^ 2)⁻¹‖ = (((M : ℝ) + 1) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    congr 2
    have : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hW : ∀ x ∈ Finset.Icc 1 P, ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      g (x + y * z)‖ ≤ (((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 (n + 1) k M ^ 2 *
          ∏ s ∈ Finset.Icc 1 (n + 1), karSigma k M s ((m : ℝ) * karL2Coef n α x s))
          ^ (((4 * k ^ 2 : ℕ) : ℝ)⁻¹) := by
    intro x _
    have hb := karL2_holder_at n m M k x hk α
    have hk0 : 4 * k ^ 2 ≠ 0 := by positivity
    set w := ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1), g (x + y * z)‖ with hw
    have hw0 : 0 ≤ w := norm_nonneg _
    have hb' : w ^ (4 * k ^ 2) ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 (n + 1) k M ^ 2 *
        ∏ s ∈ Finset.Icc 1 (n + 1), karSigma k M s ((m : ℝ) * karL2Coef n α x s) := by
      rw [hw, hgdef]; exact hb
    calc w = (w ^ (4 * k ^ 2)) ^ (((4 * k ^ 2 : ℕ) : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hw0 hk0).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hb' (by positivity)
  have hTle : ‖T‖ ≤ (((M : ℝ) + 1) ^ 2)⁻¹ * ∑ x ∈ Finset.Icc 1 P,
        (((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 (n + 1) k M ^ 2 *
          ∏ s ∈ Finset.Icc 1 (n + 1), karSigma k M s ((m : ℝ) * karL2Coef n α x s))
          ^ (((4 * k ^ 2 : ℕ) : ℝ)⁻¹) := by
    rw [hT, norm_mul, hinv]
    exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hW))
      (by positivity)
  linarith

/-! ### Step 5: Lemma 1 for `J_k(0)` -/

/-- Lemma 1 of Karacuba p. 243 for the count `J_k(0)` with `k = b_l`, in degree `d`, over
`0 ≤ y ≤ M`: the conclusion of the proved `karJ0_lemma1` with `n` replaced by `d`,
`J_k(0) < D_l (M+1)^{2k - d(d+1)/2 + d(d+1)/2 (1-1/d)^l}`. -/
def KarJ0Bound (d : ℕ) : Prop :=
  ∀ l M : ℕ, 0 < l →
    karJ0 d (d * l + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M <
      (20 * d : ℝ) ^ (((d * (d + 1) : ℕ) : ℝ) / 2 * l) *
        ((M : ℝ) + 1) ^ ((2 * ((d * l + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) : ℝ)
          - ((d * (d + 1) : ℕ) : ℝ) / 2 + ((d * (d + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (d : ℝ)) ^ l)

/-- PROVED CONDITIONAL ON KarLemma1. `KarJ0Bound d` for `d ≥ 12`, by `karJ0_lemma1`. -/
theorem karJ0Bound_of_lemma1 (h1 : KarLemma1) (d : ℕ) (hd : 12 ≤ d) : KarJ0Bound d :=
  fun l M hl => karJ0_lemma1 h1 d l M hd hl

/-- LEAF: Karacuba Lemma 1 p. 243, Vinogradov's mean value theorem [1], for the count `J_k(0)`
in the low degrees `2 ≤ d ≤ 12`. HARD. `KarLemma1` is stated only for `d ≥ 12`; Vinogradov's
theorem is proved for every degree, but the lab has not checked the explicit constants
`(20d)^{d(d+1)l/2}` below 12. For `d = 12` it follows from `KarLemma1`. This is the only input
that the case `n < 12` of Lemma 2 needs beyond the core leaf. -/
theorem leaf_karJ0_lowdeg : ∀ d : ℕ, 2 ≤ d → d ≤ 12 → KarJ0Bound d := by
  sorry

/-! ### Step 6: the core of Vinogradov's estimate -/

/-- LEAF: Karacuba Lemma 2 p. 243-244, the end of Vinogradov's proof [2] after the shift,
Taylor expansion and the two Holder steps, which are proved in `karL2_reduce`. HARD.
Given the mean value bound `KarJ0Bound (n+1)` of Lemma 1, one chooses `M` and `k = b_l`,
bounds `J_k(0)` by Lemma 1, sums over `x` the products of the sums `𝔖_s(m A_s(x))` using the
approximation `α_r = a/q + θ/q²` and Lemma 3, and does the exponent arithmetic giving
`ρ = τ/(3 n² l)` and the constant `(8n)^{0.5 n l}`. No exponential sum occurs. -/
theorem leaf_karL2_core :
    ∀ n m P : ℕ, 1 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 → KarJ0Bound (n + 1) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ∃ M k : ℕ, 1 ≤ k ∧
        (((M : ℝ) + 1) ^ 2)⁻¹ * ∑ x ∈ Finset.Icc 1 P,
          (((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 (n + 1) k M ^ 2 *
            ∏ s ∈ Finset.Icc 1 (n + 1), karSigma k M s ((m : ℝ) * karL2Coef n α x s))
            ^ (((4 * k ^ 2 : ℕ) : ℝ)⁻¹) + 2 * (M : ℝ) ^ 2 <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  sorry

/-! ### Assemblies -/

/-- PROVED from the core leaf: Lemma 2 for every `n ≥ 1` given `KarJ0Bound (n+1)`. -/
theorem karLemma2_of_J0 :
    ∀ n m P : ℕ, 1 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 → KarJ0Bound (n + 1) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hJ
  obtain ⟨M, k, hk, hlt⟩ := leaf_karL2_core n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hJ
  exact lt_of_le_of_lt (karL2_reduce n m P M k hk α) hlt

/-- PROVED from the leaves: the exact statement of `leaf_karLemma2_from_mvt`, the case
`n ≥ 12` conditional on `KarLemma1`, through `karJ0Bound_of_lemma1` in degree `n + 1`. -/
theorem karLemma2_from_mvt_steps (h1 : KarLemma1) :
    ∀ n m P : ℕ, 12 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  exact karLemma2_of_J0 n m P (by omega) hm hP α r hr2 hr a q θ hg hq hqP hθ hα
    (karJ0Bound_of_lemma1 h1 (n + 1) (by omega))

/-- PROVED from the leaves: the exact statement of `leaf_karLemma2_small`, the case
`1 ≤ n ≤ 11`, through `leaf_karJ0_lowdeg` in degree `n + 1 ≤ 12`. -/
theorem karLemma2_small_steps :
    ∀ n m P : ℕ, 1 ≤ n → n < 12 → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn hn12 hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  exact karLemma2_of_J0 n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα
    (leaf_karJ0_lowdeg (n + 1) (by omega) (by omega))

/-- Exact-type twins. -/
theorem karLemma2_from_mvt_steps_twin :
    type_of% @leaf_karLemma2_from_mvt := karLemma2_from_mvt_steps

theorem karLemma2_small_steps_twin :
    type_of% @leaf_karLemma2_small := karLemma2_small_steps

/-- PROVED from the leaves of this file: Karacuba's Lemma 2 conditional on `KarLemma1`. -/
theorem karLemma2_of_steps (h1 : KarLemma1) : KarLemma2 := by
  intro n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  rcases lt_or_ge n 12 with h | h
  · exact karLemma2_small_steps n m P hn h hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  · exact karLemma2_from_mvt_steps h1 n m P h hm hP α r hr2 hr a q θ hg hq hqP hθ hα

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karL2_reduce
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karLemma2_from_mvt_steps
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karLemma2_small_steps
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karLemma2_of_steps
